Binary search trees

Verification conditions generated for the following procedures:
(adapted from Dryad).

* Search: files bst-search-<i>.smt2
* Insert: files bst-insert-<i>.smt2
* Delete
* Find_leftmost
* Remove_root

Files:

bst.c	C code of functions verified
	compile with 'gcc -Wall -c bst.c'

to-slrdi.sh
	substitute old theory keywords to the new ones
	execute with './to-slrdi.sh <file>'

bst-<fun>-<i>.smt2
	verification condition for function <fun>
	verify with './spen -syn bst-<fun>-<i>.smt2'
