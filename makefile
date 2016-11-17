compile_all:
	gcc -O3 -fomit-frame-pointer -w -o nikolas_askitis_buffered_btrie nikolas_askitis_buffered_btrie.c nikolas_askitis_btrie_array_hash_mod.c
	gcc -O3 -fomit-frame-pointer -w -o nikolas_askitis_buffered_btree nikolas_askitis_buffered_btree.c
#quick usage quide
	@echo
	@cat USAGE_POLICY.txt;
	@echo "\nUsage  eg: ./nikolas_askitis_buffered_btrie output_file 1 insert-file01 1 search-file01"
	@echo "             ./nikolas_askitis_buffered_btree output_file 1 insert-file01 1 search-file01"
	@echo;
	@echo "Output eg: 'Array-BST 24.79 6.17 6.17 1000000 1000000' = data struct, space(MB), insert(sec), search(sec), inserted, found ";
	@echo;
	@echo "Dr. Nikolas Askitis | Copyright @ 2016 | askitisn@gmail.com"
	@echo;
clean:
	rm -rf t*[!.c]
	rm -rf n*[!.c]
	rm -rf s*[!.c]
