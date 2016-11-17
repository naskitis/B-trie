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
#include <stdarg.h>
#include <string.h>
#include <errno.h>
#include <sys/time.h>
#include <string.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <inttypes.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/stat.h>

#define true 1
#define false 0
#define in_range(x) (x < MIN_RANGE || x > MAX_RANGE) ? false : true

#define MIN_RANGE (char)32
#define MAX_RANGE (char)126

#define TO_MB 1000000
#define HASH_TB_SIZE 131072

#define get_msb(x) x>>31
#define ign_msb(x) ((x<<1)>>1)
#define set_msb(x) x|(1<<31)

#define READ_ERROR "Disk-routines error: Could not read a node from disk"
#define WRITE_EERROR "Disk-routines error: Could not write a bucket to disk"
#define WRITE_IERROR "Disk-routines error: Could not write an internal node to disk"

#define STR_LIM 512
#define ALPHABET_SIZE 256

#define INIT_TRIE_ALLOC_SIZE 65536
#define TRIE_SIZE 512

#define D_RATIO 0.76 

#define get_msb(x) x>>31
#define ign_msb(x) ((x<<1)>>1)
#define set_msb(x) x|(1<<31)

#define FILE_CREATION_PROBLEM "B-trie error: Could not create or access the required b-trie binary files"
#define INTERNAL_NODES_INACCESSABLE "B-trie error: Could not buffer the trie nodes from disk into memory"
#define MEMORY_EXHAUSTED "B-trie error: Could not allocate system memory to the process"
#define INPUT_FILE_ERROR "B-trie error: Could not read the vocabulary file"

#define E_OFFSET 2
#define C_OFFSET 4
#define D_OFFSET 6
#define K_OFFSET 8
#define BUCKET_FIELD_LENGTH 8

#define INIT_BUCKET_DSTART 264
#define EXTRA_STR_PTRS 32

#define SEARCH_HASH -1
#define BUCKET_ACQUIRED -2
#define NULL_BUCKET -3
#define IN_HASH_TABLE -5
#define STRING_CANNOT_BE_INDEXED -4

#define OVR_BUF 1056

#define TRIE_PREFIX "btrie_trie."
#define BUCKET_PREFIX "btrie_bucket."
#define STD_SUFFIX ".raw"

#define _4K_NODES  (uint32_t)4096
#define _8K_NODES  (uint32_t)8192
#define _16K_NODES (uint32_t)16384

#define TOP_DOWN 1
#define BUF_SIZE 55000
#define MEMORY_RESIDENT 3

static int insert_mode=false;

static long unsigned int strcmp_cnt=0;
static long unsigned int char_cnt=0;
static long unsigned int read_cnt=0;
static long unsigned int write_cnt=0;
static long unsigned int intern_write_cnt=0;
static long unsigned int intern_read_cnt=0;

typedef struct ds_options
{
  int32_t node_size;
  int32_t batch_mode;
  int32_t print_lost;
  int32_t print_found;
  int32_t time_only;
  int32_t insert_mode;
  int32_t summary;
  int32_t range_mode;
  int32_t memory_resident;
  int32_t table_format;
  int32_t num_pointers;

  double d_ratio;

  char vocab_filename[100];
  char output_filename[100];
  char construct_dataset[100];
  char search_dataset[100];

}ds_options;

typedef struct timeval timer;

typedef struct btrie
{
  int buckets, tries;
  char **alt_ds;
  uint16_t node_size;
  uint32_t key_found;
  uint32_t c_depth;
  uint32_t ct_addr;
  uint32_t nt_addr;
  uint32_t max_tree_height;
  uint32_t c_addr;
  uint32_t n_addr;
  uint32_t cache_entries;
  uint32_t cache_size;
  int32_t idx;
  uint32_t str_ptr_offset;
  uint32_t suffix_len;
  
  uint16_t consumed;
  uint16_t entries;
  uint32_t cache_entries2;
  uint32_t cache_size2;
  char *cache2;
  
  char *cache;
  char *prefix;
  char *suffix;
  
  char *c_bucket;
  char *n_bucket;
  char *tmp_buffer;
  char *null_bucket;

  char *defrag_str;
  uint16_t *str_ptr;

  uint32_t *c_trie;
  uint32_t *n_trie;
  uint32_t dirty;
  int32_t buffered_trie_addr;
  uint32_t btrie_modified;

  char last_char;

  uint32_t inserted;
  uint32_t found;
  uint32_t ignored;
  uint32_t restored;
  uint32_t num_split;
  double d_ratio;
  int32_t node_count;
  int32_t max_node_count;
  uint32_t free_space;
  uint32_t traversed;
  uint32_t trie_addr;
  uint32_t do_not_insert;
}btrie;

void btrie_init(btrie *, char *, uint32_t, uint32_t);
uint32_t btrie_insert(btrie *, char *);

uint32_t btrie_search(btrie *, char *);
void btrie_close(btrie *);
void btrie_flush(btrie *);
double find_average_height(btrie *ds);
uint32_t btrie_prefix_search(btrie *ds, char *prefix, int32_t);

static uint32_t full(btrie *, char *);
static int32_t binary_search(btrie *, const char *, const char *);
static void insert_string(btrie *, char *, const char  *);
static void btrie_split(btrie *);
static void distribute_keys(btrie *, char *, char *);
static uint32_t find_best_distribution(btrie *, char *);
static uint32_t get_unused_slot(btrie *);
void fatal(const char *msg);
void read_bucket(int32_t file, char *bucket, uint32_t addr, uint32_t bucket_len);
void write_bucket(int32_t file, char *bucket, uint32_t addr, uint32_t bucket_len);
void write_internal(int32_t file, char *bucket, uint32_t addr, uint32_t bucket_len);

unsigned long int get_read_count();
unsigned long int get_write_count();
void reset_io_counters();
unsigned long int get_internal_write_count();

int32_t scmp(const char *, const char *);
void scpy(char *, const char *, const uint32_t);
void node_cpy(uint32_t *, uint32_t *, uint32_t);
int32_t slen(const char  *s1);
unsigned long int get_strcmp_count();
unsigned long int get_char_count();
int32_t prefix_cmp(const char *word, const char *prefix);
void reset_str_counters();

FILE * fopen64 (const char *filename, const char *opentype);
void process_command_line(ds_options *options, int argc, char **argv);

uint32_t *trie_buffer;
int trie_buffer_capacity=62500;
int num_tries=0;
int trie_file=0;

int BUCKET_SIZE=8192;
int inserted=0;
int found=0;
char *current_bucket;
uint32_t *frequency;

int32_t prefix_cmp(const char *word, const char *prefix)
{
  int32_t pre_len=slen(prefix);
  int32_t word_len=slen(word);
  register int32_t i=0;

  if(pre_len > word_len) return 0;
  
  for(i=0; i<pre_len && i<word_len; i++)
  {
    if(prefix[i]==word[i])
      continue;
    else
      return 0;
  }

  return 1;
}

void node_cpy(uint32_t *dest, uint32_t *src, uint32_t bytes)
{
  bytes=bytes>>2;
  while(bytes != 0)
  {
    *dest++=*src++; 
    bytes--;
  } 
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

uint32_t pure_node(btrie *ds, char *bucket)
{
   char *min = (char *)bucket;
   char *max = (char *)(bucket+1);

   if(*min == *max)
   {
     return true;
   }
   else
   {
     return false;
   }
}

uint32_t get_unused_slot(btrie *ds)
{
  uint32_t n_addr = ds->cache_entries * TRIE_SIZE;

  if(n_addr >= ds->cache_size)
    if((ds->cache=realloc(ds->cache, (ds->cache_size+=(TRIE_SIZE<<7))))==NULL)
      fatal(MEMORY_EXHAUSTED);

  ds->cache_entries++;

  return n_addr/TRIE_SIZE;
}

int32_t binary_search(btrie *ds, const char *node, const char *word)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);
  int32_t mid_pnt=0, result=0, left_pnt=0, right_pnt=(*entries)-1;

  while(right_pnt >= left_pnt)
  {
    mid_pnt=(left_pnt+right_pnt)>>1;
    result=scmp(word, node+*d_start+*(key+mid_pnt)+sizeof(uint32_t));

    if(result == 0) 
    {   
      if(insert_mode)
      {
        *(uint32_t *)(node+*d_start+*(key+mid_pnt))+=1; 
      }
      ds->key_found=true; 
      return mid_pnt; 
    }
    
    if(result<0)
      right_pnt=mid_pnt-1;
    else
      left_pnt=mid_pnt+1;
  }
  return left_pnt;
}

int32_t search_index(btrie *ds, char *word, uint32_t range_mode)
{
  uint32_t *c_trie= (uint32_t *)ds->cache;
  uint32_t addr=1;
  register uint32_t i=0;
  

  ds->c_depth=ds->ct_addr=ds->key_found=ds->idx=0;
  ds->prefix[0]='\0';

  if(ds->cache_entries != 0)
  {
    while ( *(word+i) != '\0')
    {
      if(!in_range(*(word+i))) return (ds->idx=STRING_CANNOT_BE_INDEXED);

      addr=*(c_trie + (uint32_t)*(word+i));
      ds->last_char=*(word+i);

      if(addr==0) return (ds->idx=NULL_BUCKET);

      if(get_msb(addr)==0)
      {
        ds->ct_addr=addr;
        c_trie = (uint32_t *)(ds->cache + addr*TRIE_SIZE);

        ds->prefix[ds->c_depth++]=ds->last_char;
        ds->prefix[ds->c_depth]='\0';

        if(ds->c_depth > ds->max_tree_height) ds->max_tree_height=ds->c_depth;
      }
      else
      {
        if(ds->c_depth+1 > ds->max_tree_height) ds->max_tree_height=ds->c_depth+1;
	      break;
      }

      i++;
    }
 
    if(*(word+i) == '\0') return (ds->idx=SEARCH_HASH);
  }

  if(addr==0) return (ds->idx=NULL_BUCKET); 

  ds->c_addr=ign_msb(addr);
  read_bucket(ds->buckets, ds->c_bucket, ds->c_addr, ds->node_size);

  if(pure_node(ds, ds->c_bucket))
  {
    ds->prefix[ds->c_depth++]=ds->last_char;
    ds->prefix[ds->c_depth]='\0';

    char *new_word = (char *)(word+ds->c_depth);

    if(new_word[0] == '\0')
    {
      return (ds->idx=SEARCH_HASH);
    }
  }

  ds->idx=binary_search(ds, ds->c_bucket, word+ds->c_depth);
  return BUCKET_ACQUIRED;
}

void make_room(btrie *ds, char *node)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *consumed = (uint16_t *)(node+C_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);

  if( (uint16_t *)(key+*entries) == (uint16_t *)(node+*d_start))
  {
    memcpy(ds->defrag_str, node+*d_start, *consumed);
    (*d_start)=(*d_start)+EXTRA_STR_PTRS;
    memcpy(node+*d_start, ds->defrag_str, *consumed);
  }
}

uint32_t full(btrie *ds, char *node)
{
  uint16_t *consumed = (uint16_t *)(node+C_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);

  if(*d_start+*consumed > ds->node_size)
    return true;
  else
    return false;
}

void insert_string(btrie *ds, char  * node, const char  *word)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *consumed = (uint16_t *)(node+C_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);
  uint32_t idx=ds->idx;
  char *w;
  char *w_start;

  register uint32_t i=0;

  make_room(ds, node);

  for(i=*entries; i>idx; i--) *(key+i) = *(key+i-1);
  *(key+idx)=*consumed;

  *(uint32_t *)(node+*d_start+*(key+idx)) = 1;
  w = w_start = node+*d_start+*(key+idx)+sizeof(uint32_t);
    
  while( *word != '\0')
  {
    *w++=*word++;
  }
  *w=*word;
    
  (*consumed)+=  (w -  w_start) + 1 + sizeof(uint32_t);
  (*entries)++;
}

void selectively_dump_bucket(btrie *ds, char *node, char *suffix, int32_t print)
{
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);

  int32_t out_of_range=true;
  register int32_t i=0;
  char *string;

  if(pure_node(ds, node))
  {
    /* check if the string was consumed by the trie node + pure bucket */
    if(suffix[0] == '\0')
    {
      if(hash_search(ds->alt_ds, ds->prefix))
      {
        if(print) puts(ds->prefix);
	      ds->found++;
      }

      for(i=0; i<*entries; i++)
      {
        if(print) printf("%s%s\n", ds->prefix, node+*d_start+*(key+i)+sizeof(uint32_t));
        ds->found++;
      }
      return;
    }
  }

  for(i=0; i<*entries; i++)
  {
    string = node+*d_start+*(key+i)+sizeof(uint32_t);

    if(prefix_cmp(string, suffix))
    {
      out_of_range=false;

      if(print) printf("%s%s\n", ds->prefix, string);
      ds->found++;
    }
    else
    {
      if(out_of_range==false)
      {
        out_of_range=true;
        break;
      }
    }
  }
}

void dump_bucket(btrie *ds, uint32_t addr, int32_t print)
{
  char *node = ds->c_bucket;
  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);
  register int32_t i=0;

  read_bucket(ds->buckets, ds->c_bucket, addr, ds->node_size);

  if(pure_node(ds, node))
  {
    if(hash_search(ds->alt_ds, ds->prefix))
    {
      ds->found++;
      if(print) puts(ds->prefix);
    }

    for(i=0; i<*entries; i++)
    {
      if(print) printf("%s%s\n", ds->prefix, node+*d_start+*(key+i)+sizeof(uint32_t));
      ds->found++;
    }
  }
  else
  {
    ds->prefix[--ds->c_depth]='\0';

    for(i=0; i<*entries; i++)
    {
      if(print) printf("%s%s\n", ds->prefix, node+*d_start+*(key+i)+sizeof(uint32_t));
      ds->found++;
    }
  }
}

void dump_trie(btrie *ds, uint32_t c_addr, int32_t print)
{
  uint32_t n_addr=0;
  register uint32_t i=0;
  uint32_t depth=ds->c_depth;
  uint32_t prev_addr=-1;

  uint32_t *current_trie = (uint32_t *)(ds->cache+c_addr);

  if(hash_search(ds->alt_ds, ds->prefix))
  {
    ds->found++;
    if(print) puts(ds->prefix);  
  }
  
  for(i=MIN_RANGE; i<=MAX_RANGE; i++)
  {
    n_addr=*(current_trie+i);

    ds->prefix[depth]='\0';
    ds->c_depth=depth;

    if (n_addr == 0 )
    {
      ds->prefix[ds->c_depth]=i;
      ds->prefix[ds->c_depth+1]='\0';
      
      if(hash_search(ds->alt_ds, ds->prefix))
      {
        if(print) puts(ds->prefix);
	      ds->found++;
      } 
      
      ds->prefix[ds->c_depth]='\0';
      continue;
    }
    else if ( get_msb(n_addr) == 1 )
    {
      ds->prefix[ds->c_depth++]=i;
      ds->prefix[ds->c_depth]='\0';

      if(prev_addr !=  ign_msb(n_addr))
      {
        dump_bucket(ds, ign_msb(n_addr), print);
	      prev_addr=ign_msb(n_addr);
      }
    }
    else
    {
      ds->prefix[ds->c_depth++]=i;
      ds->prefix[ds->c_depth]='\0';
      dump_trie(ds, n_addr, print);
    }
  }
}

uint32_t btrie_prefix_search(btrie *ds, char *prefix, int32_t print)
{
  uint32_t previous_count = ds->found;
  insert_mode=false;
  int32_t result = search_index(ds, prefix, true);

  if(result == SEARCH_HASH)
  {
    dump_trie(ds, ds->ct_addr, print);
  }
  else if (result == NULL_BUCKET)
  {
    if(hash_search(ds->alt_ds, prefix))
    {
      if(print) puts(prefix);
      ds->found++;
    }
    
    return 2;
  }
  else if (result == STRING_CANNOT_BE_INDEXED)
  {
    if(print) printf("Unrecognized characters in: %s\n", prefix);
    return 2;
  }
  else
  {
    selectively_dump_bucket(ds, ds->c_bucket, prefix+ds->c_depth, print);
  }

  if(previous_count != ds->found)
    return true;
  else
    return false;
}

uint32_t btrie_search(btrie *ds, char *word)
{
  insert_mode=false; 
  int result = search_index(ds, word, false);

  if(result == SEARCH_HASH)
  {
     ds->key_found = hash_search(ds->alt_ds, word);
  }
  else if (result == NULL_BUCKET)
  {
    /* this is inefficient.  Basically, if a string is removed from a pure node
    during splitting, and the pure node is empty, its parent ptr will be set
    to null.  Two options, when enountered a null pointer, check hash.  Or
    when encountered a pointer which is set to say 1, then check hash table */
    ds->key_found = hash_search(ds->alt_ds, word);
  }
  else if (result == STRING_CANNOT_BE_INDEXED)
  {
    ds->ignored++;
    puts(word);
    ds->key_found=true;
    return false;
  }

  if(ds->key_found)  ds->found++;
  return ds->key_found;
}

uint32_t btrie_insert(btrie *ds ,char *word)
{
  insert_mode=true;
  search_index(ds, word, false);
  
  if(ds->key_found) 
  { 
    return false;
  }

  if(ds->idx==SEARCH_HASH)
  {
    if(hash_insert(ds->alt_ds, word, 0))
    {
      ds->inserted++;
    }
    return true;
  }
  else if (ds->idx == STRING_CANNOT_BE_INDEXED)
  {  
    ds->ignored++;
    puts("INSERTO");
    puts(word);
    
    return false;
  }

  /* this is outside the caching policy of the existing buckets,
  so it must be dealt with differently. That is, the ds->c_addr is
  still the cached bucket.  */
  if(ds->idx==NULL_BUCKET)
  {
    char c_char=ds->last_char;
    char *n_min = (char *)ds->null_bucket;
    char *n_max = (char *)(ds->null_bucket+1);
    uint16_t *c_entries = (uint16_t *)(ds->null_bucket+E_OFFSET);
    uint16_t *consumed= (uint16_t *)(ds->null_bucket + C_OFFSET);
    uint32_t *c_trie=NULL;

    register int i=0, j=0;

    ds->idx=0;
    ds->n_addr=lseek(ds->buckets, 0, SEEK_END)/ds->node_size;

    c_trie = (uint32_t *)(ds->cache + ds->ct_addr*TRIE_SIZE);
    *(c_trie + (uint32_t)c_char)=set_msb(ds->n_addr);

    for(i=c_char-1, j=0; i>=(int)MIN_RANGE; i--)
    {
      if(*(c_trie + (uint32_t)i)==0)
      {
        j=i;
        *(c_trie + (uint32_t)i)=set_msb(ds->n_addr);
      }
      else
      {
        break;
      }
    }

    if(j==0)
      *n_min=c_char;
    else
      *n_min=(char)j;

    for(i=c_char+1, j=0; i<=(int)MAX_RANGE; i++)
    {
      if(*(c_trie + (uint32_t)i)==0)
      {
        j=i;
        *(c_trie + (uint32_t)i)=set_msb(ds->n_addr);
      }
      else
      {
        break;
      }
    }

    if(j==0)
      *n_max=c_char;
    else
      *n_max=(char)j;

    if(*n_min == *n_max)
    {
      char *new_word = word+ds->c_depth+1;
   
      if(new_word[0] == '\0')
      {
        *(c_trie + (uint32_t)c_char)=0;
	
	      if(hash_insert(ds->alt_ds, word, 0))
	      {
           ds->inserted++;
         }
	       return true;
      }
      else
      {
        insert_string(ds, ds->null_bucket, new_word);
      }
    }
    else
    {

      for(i=(int32_t)*n_min; i<=(int32_t)*n_max; i++)
      {
        ds->prefix[ds->c_depth]=(char)i;
        ds->prefix[ds->c_depth+1]='\0';

	      if(hash_search(ds->alt_ds, ds->prefix))
        {
          insert_string(ds, ds->null_bucket, ds->prefix); 
	        ds->restored++;
        } 
      }
      
      insert_string(ds, ds->null_bucket, word+ds->c_depth);
    }

    write_bucket(ds->buckets, ds->null_bucket, ds->n_addr, ds->node_size);
    write_internal(ds->tries, (char *)c_trie, ds->ct_addr, TRIE_SIZE);

    ds->inserted++;
    ds->btrie_modified=false;

    *c_entries=0;
    *consumed=0;
    *n_min=(char)MIN_RANGE;
    *n_max=(char)MAX_RANGE;
    return true;
  }
  else
  {
   insert_string(ds, ds->c_bucket, word+ds->c_depth);
  }

  ds->btrie_modified=true;
  ds->inserted++;

  if(full(ds, ds->c_bucket))
    btrie_split(ds);
  else
    write_bucket(ds->buckets, ds->c_bucket, ds->c_addr, ds->node_size);
  
  return true;
}

void btrie_split(btrie *ds)
{
  non_recursive_hack:
  {
    char *c_bucket=ds->c_bucket;
    char *n_bucket=ds->n_bucket;
    char *c_min = (char *)c_bucket;
    char *c_max = (char *)(c_bucket+1);
    char *n_min = (char *)n_bucket;
    char *n_max = (char *)(n_bucket+1);

    uint16_t *c_entries = (uint16_t *)(c_bucket+E_OFFSET);
    uint16_t *n_entries = (uint16_t *)(n_bucket+E_OFFSET);
    uint32_t *c_trie = (uint32_t *)(ds->cache+ds->ct_addr*TRIE_SIZE);
    uint32_t *n_trie = NULL;

    register int32_t i=0;

    ds->num_split++;

    if(ds->cache_entries==0) ds->cache_entries++;

    ds->n_addr=lseek(ds->buckets, 0, SEEK_END)/ds->node_size;
    if(ds->n_addr==ds->c_addr)  ds->n_addr+=1; 

    if(*c_min==*c_max)
    {
      ds->nt_addr=get_unused_slot(ds);

      c_trie=(uint32_t *)(ds->cache+ds->ct_addr*TRIE_SIZE);
      n_trie=(uint32_t *)(ds->cache+ds->nt_addr*TRIE_SIZE);

      for(i=*c_min; i<=*c_max; i++) *(c_trie+i)=0;
      *(c_trie+(uint32_t)*c_min)=ds->nt_addr;

      *c_min=MIN_RANGE;
      *c_max=MAX_RANGE;

      write_internal(ds->tries, (char *)c_trie, ds->ct_addr, TRIE_SIZE);
      ds->ct_addr=ds->nt_addr;
      c_trie = n_trie;
    }

    distribute_keys(ds, c_bucket, n_bucket);
    
    if(*c_entries==0)
    {
      for(i=*c_min; i<=*c_max; i++) *(c_trie+i)=0;
      ds->n_addr=ds->c_addr;
    }
    else
      for(i=*c_min; i<=*c_max; i++) *(c_trie+i)=set_msb(ds->c_addr);

    if(*n_entries==0)
      for(i=*n_min; i <= *n_max; i++) *(c_trie+i)=0;
    else
      for(i=*n_min; i <= *n_max; i++) *(c_trie+i)=set_msb(ds->n_addr);

    if( !full(ds, c_bucket) && !full(ds, n_bucket) )
    {

      if(*c_entries !=0)
        write_bucket(ds->buckets, c_bucket, ds->c_addr, ds->node_size);
      else
      {
        ;
      }

      if(*n_entries != 0)
        write_bucket(ds->buckets, n_bucket, ds->n_addr, ds->node_size);

      write_internal(ds->tries, (char *)c_trie, ds->ct_addr, TRIE_SIZE);
      return;
    }
    else if( !full(ds, c_bucket) && full(ds, n_bucket))
    {
      if(*c_entries!=0)
      {
        write_bucket(ds->buckets, c_bucket, ds->c_addr, ds->node_size);
	      ds->c_addr=ds->n_addr;
      }

      node_cpy((uint32_t *)c_bucket, (uint32_t *)n_bucket,
                                         ds->node_size+OVR_BUF);
      goto non_recursive_hack;
    }
    else if( full(ds, c_bucket) && !full(ds, n_bucket))
    {
      if(*n_entries!=0)
        write_bucket(ds->buckets, n_bucket, ds->n_addr, ds->node_size);

      goto non_recursive_hack;
    }
    else
    {
      puts("Both nodes are full, this is bad, really bad !!!!!");
      exit(EXIT_FAILURE);
      return;
    }
  }
}

uint32_t find_best_distribution(btrie *ds, char *node)
{
  int32_t frequency[ALPHABET_SIZE];

  char min = *(char *)node;
  char max = *(char *)(node+1);

  uint16_t *entries = (uint16_t *)(node+E_OFFSET);
  uint16_t *d_start = (uint16_t *)(node+D_OFFSET);
  uint16_t *key = (uint16_t *)(node+K_OFFSET);
  int32_t o_keys=*entries;

  int32_t character=0, remaining_keys=o_keys, added_keys=0;
  double ratio=0.0;
  register int32_t i=0;

  for(i=0; i<ALPHABET_SIZE; i++)  frequency[i]=0;

  for(i=0; i<o_keys; i++)
  {
    character = (node+*d_start+*(key+i)+sizeof(uint32_t))[0];
    if(character=='\0') continue;
    frequency[ character ]++;
  }

  for(i=min; i<=max; i++)
  {
    if(frequency[i]==0) continue;

    added_keys+=frequency[i];
    remaining_keys-=frequency[i];

    if(remaining_keys==0)  return (i==min) ? i : i-1;
    ratio=added_keys/(double)remaining_keys;
    if(ratio>=ds->d_ratio)  return (i==max) ? i-1 : i;
  }
  return min + ((max - min)>>1);
}

void distribute_keys(btrie *ds, char *c_node, char *n_node)
{
  char *c_min = (char *)(c_node);
  char *c_max = (char *)(c_node+1);
  uint16_t *c_entries = (uint16_t *)(c_node+E_OFFSET);
  uint16_t *c_consumed = (uint16_t *)(c_node+C_OFFSET);
  uint16_t *c_d_start = (uint16_t *)(c_node+D_OFFSET);
  uint16_t *c_key = (uint16_t *)(c_node+K_OFFSET);

  char *n_min = (char *)n_node;
  char *n_max = (char *)(n_node+1);
  uint16_t *n_entries = (uint16_t *)(n_node+E_OFFSET);
  uint16_t *n_consumed = (uint16_t *)(n_node+C_OFFSET);
  uint16_t *n_d_start = (uint16_t *)(n_node+D_OFFSET);
  uint16_t *n_key = (uint16_t *)(n_node+K_OFFSET);
  uint32_t *copies;
  
  char *w_start;
  char *word;
  char *new_buffer;

  char tmp;

  uint32_t /* len=0,*/ n_key_ptr=0, offset=0;
  int32_t o_keys=*c_entries;
  register int32_t i=0, j=0;

  char new_min;
  char mid_char=find_best_distribution(ds, c_node);

  *n_max=*c_max;
  *c_max=mid_char;
  *n_min=(mid_char+1);

  *n_entries=0;
  *n_consumed=0;

  new_min=*n_min;

  for(i=0; i<o_keys; i++)
  {
    copies = (uint32_t *)(c_node + *c_d_start + *(c_key+i));
    w_start = word = (c_node + *c_d_start + *(c_key+i)+sizeof(uint32_t));

    if(word[0] == '\0')
    {
      hash_insert(ds->alt_ds, ds->prefix, *copies);
      (*c_entries)--;
    }
    else if(word[0] >= new_min)
    {
      if (*n_min == *n_max)
      {
        tmp = word[0];
        word=word+1;
	
        if(word[0] == '\0')
        {
          ds->prefix[ds->c_depth]=tmp;
                ds->prefix[ds->c_depth+1]='\0';
          
          hash_insert(ds->alt_ds, ds->prefix, *copies);
                (*c_entries)--; 
          
          continue; 
        }
      }
         
      *(n_key+j)=*n_consumed;
      *(uint32_t *)(ds->tmp_buffer+*n_consumed) = *copies;
      new_buffer = (ds->tmp_buffer+*n_consumed+sizeof(uint32_t));

      while( *word != '\0')
      {
        *new_buffer++=*word++;
      }
      *new_buffer=*word;

      j++;
      (*n_consumed)=*(n_consumed)+ (word -  w_start) + 1 + sizeof(uint32_t);
      (*n_entries)++;
      (*c_entries)--;
    }
    else
    {
      if (*c_min == *c_max)
      {
        tmp = word[0];
        word=word+1;
	
        if(word[0] == '\0')
        {
          ds->prefix[ds->c_depth]=tmp;
                ds->prefix[ds->c_depth+1]='\0';
            
          hash_insert(ds->alt_ds, ds->prefix, *copies);
                (*c_entries)--; 
          
          continue; 
        }
      }

      *(uint32_t *)(ds->defrag_str+offset) = *copies;
      new_buffer=(ds->defrag_str+offset+sizeof(uint32_t));
      
      while( *word != '\0')
      {
        *new_buffer++=*word++;
      }
      
      *new_buffer=*word;
      *(c_key+n_key_ptr++)=offset; 
      offset+= (word -  w_start) +1 + sizeof(uint32_t);
    }
  }

  *n_d_start=(*n_entries==0) ? (BUCKET_FIELD_LENGTH+EXTRA_STR_PTRS) :
                               (BUCKET_FIELD_LENGTH+((*n_entries)<<1)+EXTRA_STR_PTRS);

  if(*n_entries!=0)
     memcpy(n_node+*n_d_start, ds->tmp_buffer, *n_consumed);

  *c_consumed=offset;
  *c_d_start=(*c_entries==0) ? (BUCKET_FIELD_LENGTH+EXTRA_STR_PTRS) :
                               (BUCKET_FIELD_LENGTH+((*c_entries)<<1)+EXTRA_STR_PTRS);

  if(*c_entries!=0)
     memcpy(c_node+*c_d_start, ds->defrag_str, offset);
}

void btrie_init(btrie *ds, char *file_suffix, uint32_t construct_mode, uint32_t node_size)
{
  char filename[STR_LIM];
  memset(ds, 0, sizeof(btrie));
  ds->node_size=node_size;

  strcpy(filename, TRIE_PREFIX); strcat(filename, file_suffix);
  if( (ds->tries=(int32_t)open (filename, O_RDWR | O_CREAT, 0600)) <=0) fatal(FILE_CREATION_PROBLEM);

  strcpy(filename, BUCKET_PREFIX); strcat(filename, file_suffix);
  if( (ds->buckets=(int32_t)open (filename, O_RDWR | O_CREAT, 0600)) <=0) fatal(FILE_CREATION_PROBLEM);

  if( (ds->c_bucket = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->n_bucket = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->null_bucket = (char *) malloc(ds->node_size+OVR_BUF)) == NULL) fatal(MEMORY_EXHAUSTED);

  if( (ds->defrag_str  = (char *) calloc(ds->node_size+OVR_BUF, sizeof(char))) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->tmp_buffer = (char *) calloc(ds->node_size+OVR_BUF, sizeof(char))) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->prefix = (char *)calloc(STR_LIM+1, sizeof(char))) == NULL) fatal(MEMORY_EXHAUSTED);
  if( (ds->alt_ds = (char **) calloc(HASH_TB_SIZE, sizeof(char *)))==NULL) fatal(MEMORY_EXHAUSTED);

  hash_init(ds->alt_ds, file_suffix, STR_LIM);

  if((ds->cache_size=lseek(ds->tries, 0, SEEK_END))!=0)
  {
    lseek(ds->tries, 0, SEEK_SET);
    ds->cache_entries = ds->cache_size/TRIE_SIZE;
    if((ds->cache = (char *)malloc(ds->cache_size)) == NULL) fatal(MEMORY_EXHAUSTED);
    if(read(ds->tries, ds->cache, ds->cache_size)<=0) fatal(INTERNAL_NODES_INACCESSABLE);
  }
  else
  {
    ds->cache_entries=0;
    ds->cache_size=(TRIE_SIZE<<7);
    if( (ds->cache = (char *) malloc(ds->cache_size)) == NULL) fatal(MEMORY_EXHAUSTED);
    memset(ds->cache, 0, ds->cache_size);
  }

  {
  char *min = (char *)ds->c_bucket;
  char *max = (char *)(ds->c_bucket+1);
  uint16_t *entries=(uint16_t *)(ds->c_bucket + E_OFFSET);
  uint16_t *consumed= (uint16_t *)(ds->c_bucket + C_OFFSET);
  uint16_t *d_start=  (uint16_t *)(ds->c_bucket + D_OFFSET);

  *min=MIN_RANGE;
  *max=MAX_RANGE;
  *d_start=INIT_BUCKET_DSTART;
  *entries=0;
  *consumed=0;

  if(lseek(ds->buckets, 0, SEEK_END)==0)
  {
    write_bucket(ds->buckets, ds->c_bucket, 1, ds->node_size);
  }

  node_cpy((uint32_t *)ds->null_bucket, (uint32_t *)ds->c_bucket, ds->node_size);
  read_bucket(ds->buckets, ds->c_bucket, 1, ds->node_size);
  ds->c_addr=1;
  }
}

void btrie_close(btrie *ds)
{
  close(ds->tries);
  close(ds->buckets);
  free(ds->cache);
  free(ds->c_bucket);
  free(ds->n_bucket);
  free(ds->null_bucket);
  free(ds->defrag_str);
  free(ds->prefix);
  free(ds->tmp_buffer);
  hash_destroy(ds->alt_ds);
  free(ds->alt_ds);
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

double perform_insertion(btrie *ds, char *to_insert)
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
   
   /* ----- insertion  ----------------------------- */  
   getrusage(RUSAGE_SELF, &r);

   sys_start = 1000.0 * ( r.ru_stime.tv_sec) + 0.001  * (r.ru_stime.tv_usec );
   usr_start = 1000.0 * ( r.ru_utime.tv_sec) + 0.001  * (r.ru_utime.tv_usec );

   gettimeofday(&start, NULL);
    
   time_loop_insert: 

   btrie_insert(ds, buffer);

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

double perform_search(btrie *ds, char *to_search)
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
    
   btrie_search(ds, buffer);
   
   for(;  *buffer != '\0'; buffer++);
   buffer++;
   
   if(buffer - buffer_start >= input_file_size) goto search_complete;
   goto time_loop_search;
   
   search_complete:
   
   gettimeofday(&stop, NULL);
   /* --------------------------------------------------------------------------- */
   
   getrusage(RUSAGE_SELF, &r);

   sys_end = 1000.0 * ( r.ru_stime.tv_sec) + 0.001  * (r.ru_stime.tv_usec );
   usr_end = 1000.0 * ( r.ru_utime.tv_sec) + 0.001  * (r.ru_utime.tv_usec );

   sys_results_search+=(sys_end-sys_start)/1000.0;
   usr_results_search+=(usr_end-usr_start)/1000.0;

   search_real_time = 1000.0 * ( stop.tv_sec - start.tv_sec ) + 0.001  
   * (stop.tv_usec - start.tv_usec );
   search_real_time = search_real_time/1000.0;
  
   free(buffer_start); 
   return search_real_time;
}

static int unique_paths=0;
static int other=0;
void in_order(btrie *, int, int);

void in_order(btrie *ds, int addr, int depth)
{
  unsigned int *current_trie = (unsigned int *)(ds->cache+addr);
  int addr2=0, i=0;

  int local=false, local2=false, local_depth=depth;

  for(i=MIN_RANGE; i<=MAX_RANGE; i++)
  {
    addr2=*(current_trie + i);
    if(addr2==0) continue;

    if(local==false)
    {
      local_depth++;
      local=true;
    }

    if(get_msb(addr2))
    {
      if(local2==false)
      {
        unique_paths++;
	      local2=true;
	      other+=local_depth;
      }
    }
    else
    {
      in_order(ds, *(current_trie+i)*TRIE_SIZE, local_depth);
    }
  }
}

double find_average_height(btrie *ds)
{
  if(ds->cache_entries ==0 ) return 0.0;

  in_order(ds, 0, 0);
  return other/(double)unique_paths;
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
   btrie ds;
   
   int num_files=0, i=0, j=0;
   uint32_t hashed=0;
   double mem = 0, insert_real_time=0.0, search_real_time=0.0;
   
   file_out = argv[1];
   BUCKET_SIZE = 8192;
   num_files = atoi(argv[2]);
   
   btrie_init(&ds, file_out, TOP_DOWN, BUCKET_SIZE);
   ds.d_ratio=D_RATIO;
   
   ds.inserted=0;
   ds.found=0;

   reset_io_counters();
   reset_str_counters();
   reset_hash_counters();
   reset_hash_str_counters();

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
   strcmp_hash_insert=get_hash_strcmp_count();
   charcmp_hash_insert=get_hash_charcmp_count();

   hashed=get_number_of_hash_insertions();
   insert_hash_hits=get_number_of_hash_search_hits(); 
   insert_hash_miss=get_number_of_hash_search_misses();

   reset_hash_counters();
   reset_str_counters();
   reset_io_counters();
   reset_hash_str_counters();
   ds.max_tree_height=0;

   for(i=0; i<num_files; i++, j++)
   {
     to_search=argv[j];     
     search_real_time+=perform_search(&ds, to_search);
   } 
   
   found = ds.found;
   
   if(ds.inserted != 0)  fatal("Inserted during self-search");
   
   ds.found=0;
  
   uint32_t intern_size=lseek(ds.tries, 0, SEEK_END);
   uint32_t leaf_size=lseek(ds.buckets, 0, SEEK_END);

   printf("B-trie %.2f %.2f %.2f %.2f %d %d %d --- Dr. Nikolas Askitis, Copyright @ 2016, askitisn@gmail.com\n", vsize / (double) TO_MB, 
     (double)get_hash_file_size()/TO_MB + (double)leaf_size/TO_MB + (double)intern_size/TO_MB,  
     insert_real_time, search_real_time, inserted, found, BUCKET_SIZE);

   btrie_close(&ds);
   
   return 0;
}
