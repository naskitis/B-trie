/*******************************************************************************
 * // Begin statement                                                          *
 *                                                                             *
 * Author:        Dr. Nikolas Askitis                                          *
 * Email:         askitisn@gmail.com                                           *
 * Github.com:    https://github.com/naskitis                                  *
 *                                                                             *
 * Copyright @ 2016.  All rights reserved.                                     *
 *                                                                             *
 * Permission to use my software is granted provided that this statement       *
 * is retained.                                                                *
 *                                                                             *
 * My software is for non-commercial use only.                                 *
 *                                                                             *
 * If you want to share my software with others, please do so by               *
 * sharing a link to my repository on github.com.                              *
 *                                                                             *
 * If you would like to use any part of my software in a commercial or public  *
 * environment/product/service, please contact me first so that I may          *
 * give you written permission.                                                *
 *                                                                             *
 * This program is distributed without any warranty; without even the          *
 * implied warranty of merchantability or fitness for a particular purpose.    *
 *                                                                             *
 * // End statement                                                            *
 ******************************************************************************/

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdarg.h>
#include <inttypes.h>
#include <unistd.h>
#include <errno.h>
#include <fcntl.h>
#include <sys/types.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <assert.h>

#define ROOT_ADDR 0

#define TOP_DOWN 1
#define BULK 2
#define MEMORY_RESIDENT 3

#define STD_SUFFIX ".raw"
#define STR_LIM 1024

#define INTERNAL_PREFIX "btree_internal."
#define EXTERNAL_PREFIX "btree_leaf."

#define FILE_CREATION_PROBLEM "B-tree init() error: Could not access the required b-tree files"
#define INTERNAL_NODES_INACCESSABLE "B-tree init() error: Could not buffer the internal nodes from disk into memory"
#define MEMORY_EXHAUSTED "B-tree error: Could not allocate system memory to the process"
#define INPUT_FILE_ERROR "B-tree main() error: Could not read the vocabulary file"

#define E_OFFSET 0   /* number of entries */
#define C_OFFSET 2   /* number of bytes consumed */
#define D_OFFSET 4   /* the relative offset where the strings are stored, the data-start address */
#define K_OFFSET 8   /* the relative offset where the string pointers start, the key-start address */
#define N_OFFSET 10  /* the relative offset where the array of child-node pointers begins */

#define LEAF_FIELD_LENGTH 8
#define INTERNAL_FIELD_LENGTH 10

#define get_msb(x) x>>31
#define ign_msb(x) ((x<<1)>>1)
#define set_msb(x) x|(1<<31)

#define true 1
#define false 0

#define STACK_LIM 8192

#define clr_stack(ds) ds->stack_top=-1;
#define pop(ds) (ds->stack_top < 0) ? -1 : ds->stack[ds->stack_top--]
#define push(ds, value) ds->stack[++ds->stack_top]=value

#define EXTRA_STR_PTRS 32
#define EXTRA_NODE_PTRS 68
#define STR_PARAMS 24

#define OVR_BUF 1152  /* 1024 for the string, 32+68 for pointers, + 28 for alignment */
#define BUF_SIZE 55000
#define TO_MB 1000000

static int insert_mode=false;

static long unsigned int strcmp_cnt=0;
static long unsigned int char_cnt=0;
static long unsigned int read_cnt=0;
static long unsigned int write_cnt=0;
static long unsigned int intern_write_cnt=0;
static long unsigned int intern_read_cnt=0;

uint32_t inserted, found;
uint32_t NODE_SIZE=8192;

typedef struct timeval timer;
char *mid_word;

typedef struct btree
{
  int32_t internal;
  int32_t external;

  uint32_t cache_size;
  uint32_t cache_entries;
  
  uint32_t cl_addr;
  uint32_t nl_addr;

  uint32_t c_addr;
  uint32_t n_addr;
  
  int32_t *stack;
  int32_t stack_top;

  uint32_t key_found;
  uint32_t idx;
  int32_t tree_height;

  int32_t inserted;
  int32_t found;
  
  int32_t num_split;
  uint32_t INIT_LEAF_DSTART; 
  uint32_t INIT_I_DSTART; 
  uint32_t INIT_I_KSTART;  
  
  
  char *cache;
  char *c_leaf;
  char *n_leaf;

  char *defrag_str;
  char *defrag_keys;
  uint32_t node_size;
  
} btree;

void btree_init(btree *ds, const char *file_suffix, uint32_t );
void btree_close(btree *ds);
void btree_flush(btree *ds);
int btree_search(btree *ds, const char * word);
int btree_insert(btree *ds, const char * word);

static int32_t binary_search(btree *, const char *, const char *, uint32_t);
static int32_t binary_prefix_search(btree *ds, const char  *node, const char  *word, uint32_t internal_node);
static uint32_t full(btree *, char *);
static uint32_t get_unused_slot(btree *);

static void insert_string(btree *, char *, const char  *, uint32_t, uint32_t);

static void make_room(btree *, char *, uint32_t);
static void split_leaf_node(btree *, char *);
static void insert_into_internal_nodes(btree *, char  *, uint32_t, uint32_t);
static void split_internal_node(btree *, char  *, char  *, char  *);

#include <stdio.h>
#include <stdlib.h>
#include <inttypes.h>
#include <sys/types.h>
#include <unistd.h>

#define READ_ERROR "Disk-routines error: Could not read a node from disk"
#define WRITE_EERROR "Disk-routines error: Could not write a bucket to disk"
#define WRITE_IERROR "Disk-routines error: Could not write an internal node to disk"

long unsigned int get_strcmp_count()
{
  return strcmp_cnt;
}

long unsigned int get_char_count()
{
  return char_cnt;
}

void reset_str_counters()
{
  strcmp_cnt=char_cnt=0;
}


void fatal(const char *msg)
{
  puts(msg);
  exit(EXIT_FAILURE);  
}

void read_bucket(int32_t file, char *bucket, uint32_t addr, uint32_t bucket_len)
{
  lseek(file, addr*bucket_len, SEEK_SET);
  if(read(file, bucket, bucket_len)<=0) fatal(READ_ERROR);
  read_cnt++;
}

void write_bucket(int32_t file, char *bucket, uint32_t addr, uint32_t bucket_len)
{
  lseek(file, addr*bucket_len, SEEK_SET);
  if(write(file, bucket, bucket_len)<=0) fatal(WRITE_EERROR);
  write_cnt++;
}

void write_internal(int32_t file, char *bucket, uint32_t addr, uint32_t bucket_len)
{
  lseek(file, addr*bucket_len, SEEK_SET);
  if(write(file, bucket, bucket_len)<=0) fatal(WRITE_IERROR);
  intern_write_cnt++;
}

unsigned long int get_internal_read_count()
{
  return 0;
}

void reset_io_counters()
{
  read_cnt=write_cnt=intern_write_cnt=intern_read_cnt=0;
}

unsigned long int get_read_count()
{
  return read_cnt;
}

unsigned long int get_internal_write_count()
{
  return intern_write_cnt;
}

unsigned long int get_write_count()
{
  return write_cnt;
}


void node_cpy(uint32_t *dest, uint32_t *src, uint32_t bytes)
{
  register uint32_t i=0;
  uint32_t len=bytes>>2;

  while(i<len)
  {
    *(dest+i)=*(src+i);
    i++;
  }
  return;
}

int32_t slen(const char  *s1)
{
  register uint32_t i=0;
  while (*s1 != '\0')
  {
    s1++;
    i++;
  }
  return i;
}


void scpy_null(char  *dest, const char  *src)
{
  register uint32_t i=0;
  while (  (*(dest+i)=*(src+i)) != '\0') i++;
}

void scpy(char  *dest, const char  *src, const uint32_t len)
{
  register uint32_t i=0;
  while(i<len)
  {
    *(dest+i)=*(src+i);
    i++;
  }
  return;
}

int32_t scmp(const char  *s1, const char  *s2)
{
  strcmp_cnt++;

  while(*s1 != '\0'  && *s1 == *s2 )
  {
    s1++;
    s2++;
    char_cnt++;
  }

  char_cnt++;
  return( *s1-*s2 );
}

uint32_t get_unused_slot(btree *ds)
{
  if (  (ds->cache_entries * (ds->node_size+OVR_BUF))  >= ds->cache_size )
    if ( (ds->cache = (char  *) realloc(ds->cache, 
         (ds->cache_size += ((ds->node_size<<7)+(OVR_BUF<<7)))))==NULL)
       fatal(MEMORY_EXHAUSTED);

  return ds->cache_entries++;
}

void btree_init(btree *ds, const char *file_suffix, uint32_t num_pointers)
{
  char filename[STR_LIM];
  uint32_t offset=0;

  memset(ds, 0, sizeof(btree));
  ds->node_size=NODE_SIZE;

  ds->INIT_LEAF_DSTART = LEAF_FIELD_LENGTH + (num_pointers<<1);
  ds->INIT_I_DSTART = INTERNAL_FIELD_LENGTH + ((num_pointers+1)<<2) + (num_pointers<<1);
  ds->INIT_I_KSTART = INTERNAL_FIELD_LENGTH + ((num_pointers+1)<<2);
  
  strncpy(filename, INTERNAL_PREFIX, STR_LIM);
  strncat(filename, file_suffix, STR_LIM);
  if( (ds->internal=(int32_t)open (filename, O_RDWR | O_CREAT, 0600)) <=0) fatal(FILE_CREATION_PROBLEM);

  strncpy(filename, EXTERNAL_PREFIX, STR_LIM);
  strncat(filename, file_suffix, STR_LIM);
  if( (ds->external=(int32_t)open (filename, O_RDWR | O_CREAT, 0600)) <=0) fatal(FILE_CREATION_PROBLEM);

  if( (ds->c_leaf = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->n_leaf = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->defrag_str  = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->defrag_keys = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->stack = (int32_t *)calloc(STACK_LIM, sizeof(int32_t))) == NULL) fatal(MEMORY_EXHAUSTED);
  ds->stack_top=-1;
  
  if( (ds->cache_size=lseek(ds->internal, 0, SEEK_END)) !=0)
  {
    lseek(ds->internal, 0, SEEK_SET);
    ds->cache_entries = ds->cache_size/ds->node_size;
    ds->cache_size+=(OVR_BUF*ds->cache_entries);

    if( (ds->cache = (char *)malloc(ds->cache_size)) == NULL) fatal(MEMORY_EXHAUSTED);
    while(read (ds->internal, ds->cache+offset, ds->node_size)>0) offset+=(ds->node_size+OVR_BUF);
  }
  else
  {
    ds->cache_entries=0;
    ds->cache_size=(ds->node_size<<7)+(OVR_BUF<<7);

    if( (ds->cache = (char *) malloc(ds->cache_size)) == NULL) fatal(MEMORY_EXHAUSTED);
    memset(ds->cache, 0, ds->cache_size);
  }
  
  if(lseek(ds->external, 0, SEEK_END)==0)
  {
    uint16_t *entries;
    uint16_t *consumed;
    uint16_t *d_start;

    entries =  (uint16_t *)(ds->c_leaf + E_OFFSET);
    consumed = (uint16_t *)(ds->c_leaf + C_OFFSET);
    d_start =  (uint16_t *)(ds->c_leaf + D_OFFSET);

    *d_start=ds->INIT_LEAF_DSTART;
    *entries=0;
    *consumed=0;

    write_bucket(ds->external, ds->c_leaf, 0, ds->node_size);
  }
  
  read_bucket(ds->external, ds->c_leaf, 0, ds->node_size);
  ds->cl_addr=0;
  
  mid_word = (char *)calloc(NODE_SIZE, 1);
}

void btree_close(btree *ds)
{
  close(ds->internal);
  close(ds->external);
  free(ds->cache);
  free(ds->c_leaf);
  free(ds->n_leaf);
  free(ds->stack);
  free(ds->defrag_str);
  free(ds->defrag_keys);
  free(mid_word);
}

int btree_search(btree *ds, const char  *word)
{
  uint32_t addr=ROOT_ADDR;
  int32_t idx, height=0;
  char *node=ds->cache;

  clr_stack(ds);
  push(ds, addr);
  ds->key_found=false;

  if(ds->cache_entries > 0)
    while(true)
    {
      idx = binary_search(ds, node, word, true);
      addr = *(((uint32_t *)(node+N_OFFSET))+idx);

      if(get_msb(addr)==0)
      {
        node = (char  *)(ds->cache+ (addr*(NODE_SIZE+OVR_BUF)));
        push(ds, addr);
        height++;
        if(height > ds->tree_height) ds->tree_height=height;
      }
      else
      {
        height++;
        if(height > ds->tree_height) ds->tree_height=height;
        break;
      }
    }

  ds->cl_addr=ign_msb(addr);
  read_bucket(ds->external, ds->c_leaf, ds->cl_addr, ds->node_size);

  ds->idx=binary_search(ds, ds->c_leaf , word, false);
  if(ds->key_found)  ds->found++;
  
  return 1;
}

int btree_insert(btree *ds, const char *word)
{
  insert_mode=true;
  btree_search(ds, word);
  insert_mode=false;

  if(ds->key_found) 
  {
    ds->found--;
    return; 
  }

  insert_string(ds, ds->c_leaf, word, false, false);

  if(full(ds, ds->c_leaf))
  {
    split_leaf_node(ds, mid_word);

    ds->nl_addr = lseek(ds->external, 0, SEEK_END)/ds->node_size;

    write_bucket(ds->external, ds->c_leaf, ds->cl_addr, ds->node_size);
    write_bucket(ds->external, ds->n_leaf, ds->nl_addr, ds->node_size);

    insert_into_internal_nodes(ds, mid_word, pop(ds), false);
  }
  else
  {
    write_bucket(ds->external, ds->c_leaf, ds->cl_addr, ds->node_size);
  }

  ds->inserted++;
  return 1;
}

void insert_into_internal_nodes(btree *ds, char  *word, uint32_t addr, uint32_t child_was_internal)
{
  char  *n_node;
  char  *c_node = (char  *)(ds->cache + (addr*(NODE_SIZE+OVR_BUF)));
  uint16_t *c_entries =  (uint16_t *)(c_node+E_OFFSET);
  uint16_t *c_consumed = (uint16_t *)(c_node+C_OFFSET);
  uint16_t *c_d_start =  (uint16_t *)(c_node+D_OFFSET);
  uint16_t *c_k_start =  (uint16_t *)(c_node+K_OFFSET);

  ds->num_split++;
  
  if(ds->cache_entries==0)
  {
    ds->cache_entries++;
    *c_entries=0;
    *c_consumed=0;
    *c_d_start=ds->INIT_I_DSTART;
    *c_k_start=ds->INIT_I_KSTART;
  }

  insert_string(ds, c_node, word, true, child_was_internal);

  if(!full(ds, c_node))
  {
    write_internal(ds->internal, c_node, addr, ds->node_size);
    return;
  }

  if(addr==ROOT_ADDR)
  {
    ds->c_addr = get_unused_slot(ds);
    ds->n_addr = get_unused_slot(ds);

    node_cpy((uint32_t *)(ds->cache + (ds->c_addr*(NODE_SIZE+OVR_BUF))), 
             (uint32_t *)(ds->cache + ROOT_ADDR), ds->node_size+OVR_BUF);

    c_node = (char  *)(ds->cache + (ds->c_addr*(NODE_SIZE+OVR_BUF)));
    n_node = (char  *)(ds->cache + (ds->n_addr*(NODE_SIZE+OVR_BUF)));

    split_internal_node(ds, c_node, n_node, word);

    write_internal(ds->internal, c_node, ds->c_addr, ds->node_size);
    write_internal(ds->internal, n_node, ds->n_addr, ds->node_size);

    c_node = (char  *)(ds->cache+ROOT_ADDR);
    c_entries =  (uint16_t *)(c_node+E_OFFSET);
    c_consumed = (uint16_t *)(c_node+C_OFFSET);
    c_d_start =  (uint16_t *)(c_node+D_OFFSET);
    c_k_start =  (uint16_t *)(c_node+K_OFFSET);

    *c_entries=0;
    *c_consumed=0;
    *c_d_start=ds->INIT_I_DSTART;
    *c_k_start=ds->INIT_I_KSTART;

    insert_into_internal_nodes(ds, word, ROOT_ADDR, true);
  }
  else
  {
    ds->c_addr=addr;
    ds->n_addr=get_unused_slot(ds);

    c_node = (char  *)(ds->cache+ (ds->c_addr*(NODE_SIZE+OVR_BUF)));
    n_node = (char  *)(ds->cache+ (ds->n_addr*(NODE_SIZE+OVR_BUF)));

    split_internal_node(ds, c_node, n_node, word);

    write_internal(ds->internal, c_node, ds->c_addr, ds->node_size);
    write_internal(ds->internal, n_node, ds->n_addr, ds->node_size);

    insert_into_internal_nodes(ds, word, pop(ds), true);
  }
}

void split_internal_node(btree *ds, char *c_node, char *n_node, char *word)
{
  uint16_t *n_entries =  (uint16_t *)(n_node+E_OFFSET);
  uint16_t *n_consumed = (uint16_t *)(n_node+C_OFFSET);
  uint16_t *n_d_start =  (uint16_t *)(n_node+D_OFFSET);
  uint16_t *n_k_start =  (uint16_t *)(n_node+K_OFFSET);
  uint32_t *n_ptr = (uint32_t *)(n_node+N_OFFSET);
  uint16_t *n_key;

  uint16_t *c_entries =  (uint16_t *)(c_node+E_OFFSET);
  uint16_t *c_consumed = (uint16_t *)(c_node+C_OFFSET);
  uint16_t *c_d_start =  (uint16_t *)(c_node+D_OFFSET);
  uint16_t *c_k_start =  (uint16_t *)(c_node+K_OFFSET);
  uint16_t *c_key = (uint16_t *)(c_node+*c_k_start);
  uint32_t *c_ptr = (uint32_t *)(c_node+N_OFFSET);

  uint32_t o_entries=*c_entries;
  uint32_t mid_pnt = (o_entries)>>1, len=0, d_consumed=0;
  register uint32_t i=0, j=0;
  char *w;
  char *w_start;
  char *t;
  
  *n_entries=0;
  *n_consumed=0;
  *n_d_start=INTERNAL_FIELD_LENGTH + (mid_pnt<<2)+EXTRA_NODE_PTRS + (mid_pnt<<1)+EXTRA_STR_PTRS;
  *n_k_start=INTERNAL_FIELD_LENGTH + (mid_pnt<<2)+EXTRA_NODE_PTRS;
  n_key = (uint16_t *)(n_node+*n_k_start);

  scpy_null(word, c_node+*c_d_start+*(c_key+mid_pnt));

  for(i=mid_pnt+1, j=0; i<o_entries; i++, j++)
  {
    *(n_key+j)=*n_consumed; 
    w = w_start = n_node + *n_d_start + *(n_key+j);
    t = c_node + *c_d_start + *(c_key+i);
    
    while( *t != '\0')
    {
      *w++=*t++;
    }
    *w=*t;
    
    (*n_consumed) +=  (w -  w_start)+1;
    (*n_entries)++;
    (*c_entries)--;
     *(n_ptr+j) = *(c_ptr+i);
  }
  *(n_ptr+j) = *(c_ptr+i);
  (*c_entries)--;

  n_key=(uint16_t *)(ds->defrag_keys);

  for(i=0; i<*c_entries; i++)
  {
    w = w_start = ds->defrag_str+d_consumed;
    t = c_node + *c_d_start + *(c_key+i);
    
    while( *t != '\0')
    {
      *w++=*t++;
    }
    *w=*t;
    
    *(n_key+i)=d_consumed;
    d_consumed+=(w -  w_start)+1;
  }
  *c_consumed=d_consumed;

  *c_k_start=INTERNAL_FIELD_LENGTH + (mid_pnt<<2)+EXTRA_NODE_PTRS;
  memcpy(c_node+*c_k_start, ds->defrag_keys, (*c_entries)<<1);

  *c_d_start=INTERNAL_FIELD_LENGTH + (mid_pnt<<2)+EXTRA_NODE_PTRS + (mid_pnt<<1)+EXTRA_STR_PTRS;
  memcpy(c_node+*c_d_start, ds->defrag_str, d_consumed);
}

void split_leaf_node(btree *ds, char  *word)
{
  char  *n_node = ds->n_leaf;
  char  *c_node = ds->c_leaf;

  uint16_t *n_entries =  (uint16_t *)(n_node+E_OFFSET);
  uint16_t *n_consumed = (uint16_t *)(n_node+C_OFFSET);
  uint16_t *n_d_start =  (uint16_t *)(n_node+D_OFFSET);
  uint16_t *n_key =      (uint16_t *)(n_node+K_OFFSET);

  uint16_t *c_entries =  (uint16_t *)(c_node+E_OFFSET);
  uint16_t *c_consumed = (uint16_t *)(c_node+C_OFFSET);
  uint16_t *c_d_start =  (uint16_t *)(c_node+D_OFFSET);
  uint16_t *c_key =      (uint16_t *)(c_node+K_OFFSET);

  uint32_t o_entries=*c_entries;
  uint32_t mid_pnt = (*c_entries)>>1, len=0, d_consumed=0;
  register uint32_t i=0, j=0;
  char *w;
  char *w_start;
  char *t;
  
  *n_entries=0;
  *n_consumed=0;
  *n_d_start = LEAF_FIELD_LENGTH + (mid_pnt<<1)+EXTRA_STR_PTRS;

  scpy_null(word, c_node+*c_d_start+*(c_key+mid_pnt)+sizeof(uint32_t));

  for(i=mid_pnt+1, j=0; i<o_entries; i++, j++)
  {
    *(n_key+j)=*n_consumed;
    
    *(uint32_t *)(n_node + *n_d_start + *(n_key+j)) = *(uint32_t *)(c_node + *c_d_start + *(c_key+i));
    w = w_start = n_node + *n_d_start + *(n_key+j)+sizeof(uint32_t);
    t = c_node + *c_d_start + *(c_key+i)+sizeof(uint32_t );
    
    while( *t != '\0')
    {
      *w++=*t++;
    }
    *w=*t;
    
    (*n_consumed) +=  (w -  w_start)+1 + sizeof(uint32_t);
    (*n_entries)++;
    (*c_entries)--;
  }

  for(i=0; i<=mid_pnt; i++)
  {
    *(uint32_t *)(ds->defrag_str+d_consumed) = *(uint32_t *)(c_node + *c_d_start + *(c_key+i));
    w = w_start = ds->defrag_str+d_consumed + sizeof(uint32_t);
    t = c_node + *c_d_start + *(c_key+i) + sizeof(uint32_t);
    
    while( *t != '\0')
    {
      *w++=*t++;
    }
    *w=*t;
    
    *(c_key+i)=d_consumed; 
    d_consumed += ((w -  w_start)+1) + sizeof(uint32_t);   
  }

  *c_consumed=d_consumed;
  *c_d_start = LEAF_FIELD_LENGTH + (mid_pnt<<1)+EXTRA_STR_PTRS;
  memcpy(c_node+*c_d_start, ds->defrag_str, d_consumed);
}

uint32_t full(btree *ds, char* node)
{
  uint16_t *consumed = (uint16_t *)(node+C_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);

  if(*d_start+*consumed > ds->node_size)
    return true;
  else
    return false;
}

void insert_string(btree *ds, char  * node, const char  *word, uint32_t internal_node,
                   uint32_t child_was_internal)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *consumed = (uint16_t *)(node+C_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);
  uint32_t len=0, idx=ds->idx;
  register uint32_t i=0;
  char *w;
  char *w_start;
  
  make_room(ds, node, internal_node);

  if(internal_node)
  {
    uint32_t *ptr = (uint32_t *)(node+N_OFFSET);
    key = (uint16_t *) (node+*key);

    idx=binary_search(ds, node, word, internal_node);

    for(i=*entries; i>idx; i--)  { *(key+i) = *(key+i-1); *(ptr+i+1) = *(ptr+i); }

    *(key+idx)=*consumed;
    *(ptr+i)=  (child_was_internal) ? ds->c_addr : set_msb(ds->cl_addr);
    *(ptr+i+1)=(child_was_internal) ? ds->n_addr : set_msb(ds->nl_addr);

    w = w_start = node+*d_start+*(key+idx);
    
    while( *word != '\0')
    {
      *w++=*word++;
    }
    *w=*word;
    
    (*consumed) +=  (w -  w_start)+1;
    (*entries)++;
  }
  else
  {
    for(i=*entries; i>idx; i--) *(key+i) = *(key+i-1);
    *(key+idx)=*consumed;
    
    *(uint32_t *)(node+*d_start+*(key+idx)) = 1;
    w = w_start = node+*d_start+*(key+idx)+sizeof(uint32_t);
    
    while( *word != '\0')
    {
      *w++=*word++;
    }
    *w=*word;
    
    (*consumed)+=  (w -  w_start)+1 + sizeof(uint32_t);
    (*entries)++;
  }
}

void make_room(btree *ds, char  *node, uint32_t internal_node)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *consumed = (uint16_t *)(node+C_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);

  if(internal_node)
  {
    uint16_t *k_start = (uint16_t *)(node+K_OFFSET);
    key = (uint16_t *) (node+*k_start);

    if( (uint16_t *)(key+*entries) == (uint16_t *) (node+*d_start))
    {
      memcpy(ds->defrag_str, node+*d_start, *consumed);
      (*d_start)+=(EXTRA_STR_PTRS+EXTRA_NODE_PTRS);

      memcpy(node+*d_start, ds->defrag_str, *consumed);
      memcpy(ds->defrag_str, node+*k_start, (*entries)<<1);
      (*k_start)+=(EXTRA_NODE_PTRS);

      memcpy(node+*k_start, ds->defrag_str, (*entries)<<1);
    }
  }
  else
  {
    if( (uint16_t *)(key+*entries) == (uint16_t *)(node+*d_start))
    {
      memcpy(ds->defrag_str, node+*d_start, *consumed);
      (*d_start)+=EXTRA_STR_PTRS;
      memcpy(node+*d_start, ds->defrag_str, *consumed);
    }
  }
}

int32_t binary_search(btree *ds, const char  *node, const char  *word, uint32_t internal_node)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);
  int32_t mid_pnt=0, result=0, left_pnt=0, right_pnt=(*entries)-1;
  
  if(internal_node)
    key = (uint16_t *) (node+*key);

  while(right_pnt >= left_pnt)
  {
    mid_pnt=(left_pnt+right_pnt)>>1;

    if(internal_node==false)
    {
       result=scmp(word, node+*d_start+*(key+mid_pnt)+sizeof(uint32_t));

       if(result == 0)
       {
         if(insert_mode) *(uint32_t *)(node+*d_start+*(key+mid_pnt)) += 1;
         ds->key_found=true;
         return mid_pnt;
       }
    }
    else
    {
       result=scmp(word, node+*d_start+*(key+mid_pnt));

       if(result == 0)
       {
         return mid_pnt;
       }
    }

    if(result < 0)
      right_pnt=mid_pnt-1;
    else
      left_pnt=mid_pnt+1;
  }
  return left_pnt;
}


void set_terminator(char *buffer, int length)
{
  int i=0;
  for(; i<length; i++)  if( *(buffer+i) == '\n' )   *(buffer+i) = '\0';
}

double sys_start=0.0;
double sys_end=0.0;
double sys_results_insert=0.0;
double sys_results_search=0.0;
double usr_start=0.0;
double usr_end=0.0;

double usr_results_insert=0.0;
double usr_results_search=0.0;


double perform_insertion(btree *ds, char *to_insert)
{ 
   uint32_t input_file=0;
   uint32_t input_file_size=0;
   struct rusage r;

   char *buffer=0;
   char *buffer_start=0;
   
   timer start, stop;
   double insert_real_time=0.0;
   
   if( (input_file=(int32_t) open(to_insert, O_RDONLY))<=0) 
     fatal("Cant open dataset");  
     
   input_file_size=lseek(input_file, 0, SEEK_END);
     
   if( (buffer = (char *)calloc(1, input_file_size+1 )) == NULL) 
     fatal(MEMORY_EXHAUSTED);
     
   buffer_start=buffer;
   
   lseek(input_file, 0, SEEK_SET);
   read(input_file, buffer, input_file_size);
   close(input_file);
   
   set_terminator(buffer, input_file_size);
   

   getrusage(RUSAGE_SELF, &r);

   sys_start = 1000.0 * ( r.ru_stime.tv_sec) + 0.001  * (r.ru_stime.tv_usec );
   usr_start = 1000.0 * ( r.ru_utime.tv_sec) + 0.001  * (r.ru_utime.tv_usec );

   /* ----- insertion  ----------------------------- */  
   gettimeofday(&start, NULL);
    
   time_loop_insert: 

   btree_insert(ds, buffer);
   
   for(; *buffer != '\0'; buffer++);
   buffer++;
   
   if(buffer - buffer_start >= input_file_size) goto insertion_complete;
   goto time_loop_insert;

   insertion_complete:
   
   gettimeofday(&stop, NULL);

   getrusage(RUSAGE_SELF, &r);

   sys_end = 1000.0 * ( r.ru_stime.tv_sec) + 0.001  * (r.ru_stime.tv_usec );
   usr_end = 1000.0 * ( r.ru_utime.tv_sec) + 0.001  * (r.ru_utime.tv_usec );

   sys_results_insert+=(sys_end-sys_start)/1000.0;
   usr_results_insert+=(usr_end-usr_start)/1000.0;

   /* ------------------------------------- */
   
   insert_real_time = 1000.0 * ( stop.tv_sec - start.tv_sec ) + 0.001  
   * (stop.tv_usec - start.tv_usec );
   insert_real_time = insert_real_time/1000.0;

   free(buffer_start);
   return insert_real_time;
}

double perform_search(btree *ds, char *to_search)
{
   uint32_t input_file=0;
   uint32_t input_file_size=0;
   struct rusage r;

   char *buffer=0;
   char *buffer_start=0;

   timer start, stop;
   double search_real_time=0.0;

   if( (input_file=(int32_t)open (to_search, O_RDONLY)) <= 0 ) 
     fatal("Cant open dataset"); 
    
   input_file_size=lseek(input_file, 0, SEEK_END);

   if( (buffer = (char *)calloc(1, input_file_size+1 )) == NULL) 
     fatal(MEMORY_EXHAUSTED);  
     
   buffer_start=buffer;
   lseek(input_file, 0, SEEK_SET);
   read(input_file, buffer, input_file_size);
   close(input_file);
   
   set_terminator(buffer, input_file_size); 

   getrusage(RUSAGE_SELF, &r);

   sys_start = 1000.0 * ( r.ru_stime.tv_sec) + 0.001  * (r.ru_stime.tv_usec );
   usr_start = 1000.0 * ( r.ru_utime.tv_sec) + 0.001  * (r.ru_utime.tv_usec );

   /* ------ search ----------------------------------- */
   gettimeofday(&start, NULL);
    
   time_loop_search:
    
   btree_search(ds, buffer); 
   
   for(;  *buffer != '\0'; buffer++);
   buffer++;
   
   if(buffer - buffer_start >= input_file_size) goto search_complete;
   goto time_loop_search;
   
   search_complete:
   
   gettimeofday(&stop, NULL);

   getrusage(RUSAGE_SELF, &r);

   sys_end = 1000.0 * ( r.ru_stime.tv_sec) + 0.001  * (r.ru_stime.tv_usec );
   usr_end = 1000.0 * ( r.ru_utime.tv_sec) + 0.001  * (r.ru_utime.tv_usec );
   /* --------------------------------------------------------------------------- */
   

   sys_results_search+=(sys_end-sys_start)/1000.0;
   usr_results_search+=(usr_end-usr_start)/1000.0;

   search_real_time = 1000.0 * ( stop.tv_sec - start.tv_sec ) + 0.001  
   * (stop.tv_usec - start.tv_usec );
   search_real_time = search_real_time/1000.0;
  
   free(buffer_start); 
   return search_real_time;
}

int main(int argc, char **argv)
{
   long unsigned int io_ext_insert_write=0;
   long unsigned int io_ext_insert_read=0;
   long unsigned int io_int_insert_write=0;
   long unsigned int io_int_insert_read=0;
   long unsigned int strcmp_insert=0;
   long unsigned int charcmp_insert=0;
   long unsigned int strcmp_hash_insert=0;
   long unsigned int charcmp_hash_insert=0;
   long unsigned int insert_hash_hits=0;
   long unsigned int insert_hash_miss=0;

   char *to_insert=0, *to_search=0, *file_out=0;
   btree ds;
   
   int num_files=0, i=0, j=0;
   double mem = 0, insert_real_time=0.0, search_real_time=0.0;
   
   file_out = argv[1];
   NODE_SIZE = 8192; 
   num_files = atoi(argv[2]);
   
   btree_init(&ds, file_out, 128);

   ds.inserted=0;
   ds.found=0;

   reset_io_counters();
   reset_str_counters();

   for(i=0, j=3; i<num_files; i++, j++)
   {
     to_insert=argv[j];     
     insert_real_time+=perform_insertion(&ds, to_insert);
   }
   
   uint64_t vsize=0;
   {
     pid_t mypid;
     FILE * statf;
     char fname[1024];
     uint64_t ret;
     uint64_t pid; 
     char commbuf[1024];
     char state;
     uint64_t ppid, pgrp, session, ttyd, tpgid;
     uint64_t flags, minflt, cminflt, majflt, cmajflt;
     uint64_t utime, stime, cutime, cstime, counter, priority;
     uint64_t timeout, itrealvalue;
     uint64_t starttime;
     uint64_t rss, rlim, startcode, endcode, startstack, kstkesp, ksteip;
     uint64_t signal, blocked, sigignore, sigcatch;
     uint64_t wchan;
     uint64_t size, resident, share, trs, drs, lrs, dt;
    
     mypid = getpid();
     snprintf(fname, 1024, "/proc/%u/stat", mypid);
     statf = fopen(fname, "r");
     ret = fscanf(statf, "%lu %s %c %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu "
       "%lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu %lu",
       &pid, commbuf, &state, &ppid, &pgrp, &session, &ttyd, &tpgid,
       &flags, &minflt, &cminflt, &majflt, &cmajflt, &utime, &stime,
       &cutime, &cstime, &counter, &priority, &timeout, &itrealvalue,
       &starttime, &vsize, &rss, &rlim, &startcode, &endcode, &startstack,
       &kstkesp, &ksteip, &signal, &blocked, &sigignore, &sigcatch,
       &wchan);
      
     if (ret != 35) {
        fprintf(stderr, "Failed to read all 35 fields, only %d decoded\n",
          ret);
     }
     fclose(statf);
   }
  
   inserted=ds.inserted;
   ds.inserted=0;

   if(num_files==0) j++;
   
   num_files = atoi(argv[j++]);

   io_ext_insert_write=get_write_count(),
   io_ext_insert_read=get_read_count();
   io_int_insert_write=get_internal_write_count();
   io_int_insert_read=get_internal_read_count();

   strcmp_insert=get_strcmp_count();
   charcmp_insert=get_char_count();

   reset_str_counters();
   reset_io_counters();

   for(i=0; i<num_files; i++, j++)
   {
     to_search=argv[j];     
     search_real_time+=perform_search(&ds, to_search);
   }
   found = ds.found;
   
   if(ds.inserted != 0)  fatal("Inserted during self-search");
   
   ds.found=0;
   
   uint32_t intern_size=lseek(ds.internal, 0, SEEK_END);
   uint32_t leaf_size=lseek(ds.external, 0, SEEK_END);

   printf("B-tree %.2f %.2f %.2f %.2f %d %d %d --- Dr. Nikolas Askitis, Copyright @ 2016, askitisn@gmail.com\n", vsize / (double) TO_MB, 
     (double)leaf_size/TO_MB + (double)intern_size/TO_MB,
     insert_real_time, search_real_time, inserted, found, NODE_SIZE);

   btree_close(&ds);
   return 0;
}
