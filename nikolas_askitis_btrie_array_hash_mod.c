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
#include <sys/time.h>
#include <sys/resource.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <unistd.h>
#include <stdarg.h>
#include <inttypes.h>

int snprintf(char *str, size_t size, const char *format, ...);

typedef struct timeval timer;

#define true  1
#define false 0

#define MEMORY_EXHAUSTED   "Out of memory"
#define BAD_INPUT          "Bad params"
#define BUFFER_SIZE        1100000000  
#define FILE_TOO_BIG       "File too big"

#define SKIPPING
#define EXACT_FIT

#define _32_BYTES 32
#define _64_BYTES 64
#define OPTIMAL_BUFFER_SIZE 4096
#define HASH_MEMORY_EXHAUSTED "mtf-hash error: Could not allocate memory for hash table"
#define HASH_FILE_CREATE "mtf-hash error: Could not create the hash table file on disk"
#define HASH_FILE_PREFIX "btrie_hash."

uint32_t NUM_SLOTS=131072, hash_mem=0, 
         mtf_threshold=0, mtf_counter=0, ignored=0, mtf_threshold_basevalue=0;

long unsigned int hashed=0;
long unsigned int search_hit=0;
long unsigned int search_miss=0;

static FILE *hash_io=NULL;
static uint32_t shadow_to_disk=true;
static uint32_t idx=0;
uint32_t hash_file_size=0;

 uint32_t bitwise_hash(char *word);
void hash_destroy(char **ds);
uint32_t get_hash_file_size();
uint32_t hash_search(char **ds, char *word);
uint32_t hash_insert(char **ds, char *word, uint32_t);
void hash_init(char **ds, const char *file_suffix, const uint32_t STR_LIM);
uint32_t get_hash_table_memory();
long unsigned int get_number_of_hash_insertions();
long unsigned int get_number_of_hash_search_hits();
long unsigned int get_number_of_hash_search_misses();
long unsigned int strcmp_counter=0;
long unsigned int charcmp_counter=0;

void reset_hash_str_counters()
{
  strcmp_counter=0;
  charcmp_counter=0;
}

long unsigned int get_hash_strcmp_count()
{
  return strcmp_counter;
}

long unsigned int get_hash_charcmp_count()
{
  return charcmp_counter;
}

void reset_hash_counters()
{
  search_hit=search_miss=hashed=0;
}

uint32_t get_hash_table_memory()
{
  return hash_mem;
}

long unsigned int get_number_of_hash_insertions()
{
  return hashed;
}

long unsigned int get_number_of_hash_search_hits()
{
  return search_hit;
}

long unsigned int get_number_of_hash_search_misses()
{
  return search_miss;
}

static void fatal(char *str) { puts(str); exit(1); }

static void node_cpy(uint32_t *dest, uint32_t *src, uint32_t bytes)
{
  bytes=bytes>>2;
  while(bytes != 0)
  {
    *dest++=*src++; 
    bytes--;
  } 
}

void make_aligned_space(char **hash_table, uint32_t idx, uint32_t array_offset, 
                        uint32_t required_increase)
{
  if(array_offset == 0)
  {
#ifdef EXACT_FIT
    *(hash_table + idx) = malloc(required_increase);
    hash_mem += required_increase + 8;
#else    
    if(required_increase <= _32_BYTES)
    {
      if ( (*(hash_table + idx) = (char *) malloc(_32_BYTES)) == NULL) fatal(MEMORY_EXHAUSTED);  
      hash_mem += _32_BYTES + 8;  
    }
    else
    {
      uint32_t number_of_blocks = ((int)( (required_increase-1) >> 6)+1);   

      if ( (*(hash_table + idx) = (char *) malloc(number_of_blocks << 6)) == NULL) 
         fatal(MEMORY_EXHAUSTED);
	 
      hash_mem += (number_of_blocks << 6) + 8;  
    }    
#endif
  }
  else
  {
#ifdef EXACT_FIT
    char *tmp = malloc(array_offset+required_increase);
    memcpy(tmp, *(hash_table + idx), array_offset+1); 
    free( *(hash_table + idx) );
    *(hash_table + idx) = tmp;
    
 
    hash_mem = hash_mem - 1 + required_increase;
    
#else /* start of block 1 */   
    uint32_t old_array_size = array_offset + 1;
    uint32_t new_array_size = (array_offset+required_increase);
    
    if ( old_array_size <= _32_BYTES  &&  new_array_size <= _32_BYTES )
    {
      return;
    }
    else if ( old_array_size <= _32_BYTES  &&  new_array_size <= _64_BYTES)
    {  
#ifdef MALLOC
      char *tmp = malloc(_64_BYTES);
      memcpy( tmp,  *(hash_table + idx), old_array_size); 
      free( *(hash_table + idx) );
      *(hash_table + idx) = tmp;
#else
      if ( (( *(hash_table+idx) = realloc ( *(hash_table+idx), _64_BYTES)) ) == NULL )  
        fatal(MEMORY_EXHAUSTED);
#endif
      hash_mem += _32_BYTES;
      return;
    }
    else if  (old_array_size <= _64_BYTES && new_array_size <= _64_BYTES )
    {
      return;
    }
    else
    {
      uint32_t number_of_blocks = ((int)( (old_array_size-1) >> 6) + 1);
      uint32_t number_of_new_blocks = ((int)( (new_array_size-1) >> 6) + 1);

      if(number_of_new_blocks > number_of_blocks)
      {
#ifdef MALLOC
        char *tmp = malloc(number_of_new_blocks << 6);
        node_cpy( (uint32_t *) tmp, (uint32_t *) *(hash_table + idx), number_of_blocks<<6); 
        free( *(hash_table + idx) );
        *(hash_table + idx) = tmp;
#else
        if ( (( *(hash_table+idx) = realloc ( *(hash_table+idx), number_of_new_blocks << 6)) ) == NULL )
          fatal(MEMORY_EXHAUSTED);
#endif      
        hash_mem += ((number_of_new_blocks-number_of_blocks)<<6); 
      } 
    } 
#endif /* end of block 1 */

  }
}

/* 
 * The original bitwise hash function was developed by Prof. Justin Zobel.
 * The bitwise hash function below is my edit of the original code to enable
 * more efficient modulus calculations. 
 */
uint32_t bitwise_hash(char *word)
{
  char c; unsigned int h= 220373;
  for ( ; ( c=*word ) != '\0'; word++ ) h ^= ((h << 5) + c + (h >> 2));
  return((unsigned int)((h&0x7fffffff) & (NUM_SLOTS-1)));
}

void hash_destroy(char **ds)
{
  register uint32_t i=0; 
  uint32_t entries;
  uint32_t *param;
  uint32_t len=0;
  
  char *array;
  char *copy = calloc(1000000, sizeof(char));
  
  memset(copy, '\0', 1000000);
  
  rewind(hash_io);

  for(i=0; i<NUM_SLOTS; i++) 
  {
    if ( (array=*(ds+i)) != NULL) 
    {
       entries = *(uint32_t *)array;
       array += sizeof(uint32_t);
       
       loop:
   
       param = (uint32_t *) array;
       array += sizeof(uint32_t);

       if( (len = (unsigned int) *array ) >= 128)
       {
         len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) & 0xff );
       }
       array++;

       strncpy(copy, array, len);

       fprintf(hash_io, "%s\n%u\n", copy, *param);
       
       memset(copy, '\0', 1000000);
       
       array = array + len;
   
       entries--;

       
       if (entries==0) 
       {  
         free( *(ds+i) );
	       continue;
       }
   
       goto loop; 
    } 
  }   
         
  fflush(hash_io);
  fclose(hash_io);
  free(copy);
}

uint32_t get_hash_file_size()
{
   fflush(hash_io);
   fseek(hash_io, 0L, SEEK_END);
   return ftell(hash_io);
}

uint32_t hash_search(char **hash_table, char *query_start)
{
   char *array, *query=query_start;
   char *word_start;
   
   uint32_t entries;
   uint32_t *param;
   
#ifdef MTF_ON
   char *array_start;
   char *word_start_with_len;
#endif  
   uint32_t register len=0;
   
   if( (array = *(hash_table + bitwise_hash(query_start)) ) == NULL)  
   { 
     if(shadow_to_disk) search_miss++;
     return false; 
   }
   
   entries = *(uint32_t *)array;
   array += sizeof(uint32_t);
  
#ifdef MTF_ON 
   array_start=array;
#endif 

   loop:
   
   param = (uint32_t *) array;
   array += sizeof(uint32_t);
   
   query=query_start; 
   
#ifdef MTF_ON   
   word_start_with_len=array;
#endif
   
#ifdef SKIPPING
   if( (len = (unsigned int) *array ) >= 128)
   {
     len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) & 0xff );
   }
   array++;
#endif

#ifdef SKIPPING
   word_start = array;
#endif
   
   for (; *query != '\0' && *query == *array; query++, array++);
 
   strcmp_counter++;
   charcmp_counter+= (array-word_start);

#ifdef SKIPPING     
   if ( *query == '\0' && (array-word_start) == len ) 
   { 
#else
   if ( *query == '\0' && *array == '\0') 
   { 
#endif
     
#ifdef MTF_THRESHOLD
     if( --mtf_threshold == 0)
     {
       mtf_threshold=mtf_threshold_basevalue;
#endif
       
#ifdef MTF_ON	 
       if( word_start_with_len != array_start )
       {    
	 if( len < 128 )   
         {
	   memmove(array_start + len + 1, array_start, (word_start_with_len-array_start));
	   memcpy (array_start + 1, query_start, len);
	   
           *array_start = (char) len;
         }
         else
         {
	   memmove(array_start + len + 2, array_start, (word_start_with_len-array_start));
	   memcpy (array_start + 2, query_start, len);
	   
           *array_start = (char) ( len >> 8 ) | 0x80;
           *(array_start+1) = (char) ( len ) & 0xff; 
         }
	   
	 mtf_counter++;
       }
#endif    

#ifdef MTF_THRESHOLD        
     }
#endif

     search_hit++;
     
     return *param;
   }
   
#ifdef SKIPPING   
   array = word_start + len;
#else
   for(; *array!='\0'; array++);
   array++;
#endif
   
   entries--;

   if (entries==0) 
   {  
     if(shadow_to_disk) search_miss++;
     return false;
   }
   
   goto loop; 
}

uint32_t hash_insert(char **hash_table, char *query_start, uint32_t given_param)
{  
   char *array, *array_start, *query=query_start;
   char *word_start;
   uint32_t *entries;
   uint32_t entries_cpy=0;
   uint32_t *param;
   
#ifdef MTF_ON
   char *word_start_with_len;
#endif   

   uint32_t array_offset;
   uint32_t register len, idx;
         
   idx=bitwise_hash(query_start);
   
   
   if( (array = *(hash_table + idx)) == NULL)  
   {  
     array_start=array;
     goto insert;
   }
  
   entries = (uint32_t *)array;
   entries_cpy=*entries;
   array += sizeof(uint32_t);
   
   array_start=array;

   loop:
   
   param = (uint32_t *) array;
   array += sizeof(uint32_t);
  
   query=query_start; 

#ifdef MTF_ON   
   word_start_with_len=array;
#endif
   
#ifdef SKIPPING
   if( ( len = (unsigned int) *array ) >= 128 )
   {
     len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) & 0xff );
   }
   array++;
#endif

#ifdef SKIPPING
   word_start = array;
#endif

   for (; *query != '\0' && *query == *array; query++, array++);

   strcmp_counter++;
   charcmp_counter+= (array-word_start);

#ifdef SKIPPING
   if ( *query == '\0' && (array-word_start) == len ) 
   { 
#else
   if ( *query == '\0' && *array == '\0' ) 
   { 
#endif
         
#ifdef MTF_THRESHOLD
     if( --mtf_threshold == 0)
     {
       mtf_threshold=mtf_threshold_basevalue;
#endif
       
#ifdef MTF_ON	 
       if( word_start_with_len != array_start)
       {    
         if( len < 128 )   
         {
           memmove(array_start + len + 1, array_start, (word_start_with_len-array_start));
           memcpy (array_start + 1, query_start, len);
	   
           *array_start = (char) len;
         }
         else
         {
           memmove(array_start + len + 2, array_start, (word_start_with_len-array_start));
           memcpy (array_start + 2, query_start, len);
	   
           *array_start = (char) ( len >> 8 ) | 0x80;
           *(array_start+1) = (char) ( len ) & 0xff; 
         }
	   
      	 mtf_counter++;
       }
#endif

#ifdef MTF_THRESHOLD
     }
#endif

     *param += 1;
     return false;   
   }
   
#ifdef SKIPPING   
   array = word_start + len;
#else
   for(; *array!='\0'; array++);
   array++;
#endif
 
   entries_cpy--;
   
   if (entries_cpy == 0) 
   {  
     goto insert;
   }
   
   goto loop; 
  
   insert:
 
   for(; *query != '\0'; query++);
   
   len = query - query_start;
   array_offset = array-array_start;
   
   
   if(array_offset == 0)
   {
     make_aligned_space(hash_table, idx, array_offset, (( len < 128 ) ? len+2 : len+3)+(sizeof(uint32_t)*2));
     array = *(hash_table+idx);
   
     entries = (uint32_t *)array;
   
     *entries=0;
     array += sizeof(uint32_t);
   }
   else
   {
     make_aligned_space(hash_table, idx, array_offset+sizeof(uint32_t), (( len < 128 ) ? len+2 : len+3)+sizeof(uint32_t));
     
     array = *(hash_table+idx);
   
     entries = (uint32_t *)array;
     array += sizeof(uint32_t);
   }
   
   array_start = array;
   array += array_offset;
   
   param = (uint32_t *) array;
   array += sizeof(uint32_t);
   
#ifdef SKIPPING   
   if( len < 128 )
   {
     *array = (char) len;
   }
   else 
   {
     *array     = (char) ( len >> 8) | 0x80;
     *(++array) = (char) ( len ) & 0xff; 
   }
   array++;
#endif
   
   query=query_start;

   while( *query_start != '\0')
   {
     *array++ = *query_start++;
   }
   *array='\0';
   
   if(given_param == 0)
   {
     *param=1;
   }
   else
   {
     *param=given_param;
   }
   
   *entries += 1;
   
   if(shadow_to_disk)
   {
     fprintf(hash_io, "%s\n%u\n", query, *param);
     hashed++;
   }
  
   return true;    
}

#ifdef MEM_STATS
void mem_stats(char **ds)
{  
  char *array=NULL;
  int num_chains=0, char_count=0, over_space=0;
  uint32_t i=0, j=0;
  int num_null=0;
  unsigned int len=0;
  
  for(i=0; i<NUM_SLOTS; i++) 
  {
    if ( ds[i] != NULL) 
    {
      array = ds[i];
      num_chains++; 
      
      j=8;
      
      while(1)  
      {
        if( (len = (unsigned int) *array ) >= 128)
        {
          len = (unsigned int) ( ( *array & 0x7f ) << 8 ) | (unsigned int) ( *(++array) & 0xff );
          j++;
	      }
        array++;
        j++;
	
	      array=array+len;
	      j+=len;
	
        if(*array=='\0') { j++; break;}
      }
     
      char_count += j;
    }
    else
    {
      num_null++;
    }
    
  }
  
  printf("cc:%.2f, null:%d, used:%d, avg:%.2f, ", (float) (char_count + (sizeof(char *) * NUM_SLOTS) + 8)/1000000, num_null, num_chains, (float) hashed / num_chains);
  
#ifdef EXACT_FIT
  printf("ov:%s, ", "-");
#else
  printf("ov:%.2f, ", (float)(hash_mem-char_count)/1000000);
#endif
}
#endif

void hash_init(char **ds, const char *file_suffix, const uint32_t STR_LIM)
{
   register uint32_t i=0, len = 0;
   char input_buffer[OPTIMAL_BUFFER_SIZE];
   char *hash_filename=calloc(STR_LIM, sizeof(char));
   uint32_t param=0;
   
   if(hash_filename==NULL) fatal(HASH_MEMORY_EXHAUSTED);

   strncpy(hash_filename, HASH_FILE_PREFIX, STR_LIM>>1);
   strncat(hash_filename, file_suffix, STR_LIM>>1);

   hash_mem = NUM_SLOTS*sizeof(uint32_t)+8;

   if((hash_io=fopen(hash_filename, "r+")) == NULL)
   {
     if( (hash_io=fopen(hash_filename, "w+")) == NULL) fatal(HASH_FILE_CREATE);
   }
   else
   {
     shadow_to_disk=false;
     while(fscanf(hash_io, "%s\n%u\n", input_buffer, &param)!=EOF)
     {
       hash_insert(ds, input_buffer, param);
     }
   }
   shadow_to_disk=true;
   fflush(hash_io);
   
   free(hash_filename);  
}
