/****** Sorted list
 *
 */

/************************************************************************
Name: Node
Description: Structure of a node in a binary search tree
*************************************************************************/
struct Node {
struct Node* next; // next pointer field
int data; // Data field
};


/************************************************************************
Name: search
Description: Search a data value in a list.
Input: A root pointer ÕrootÕ of the list and data value v.
Output: true if the data value is found, otherwise false.
*************************************************************************/

int search(struct Node* root, int key){
	struct Node *cur = root;
	while (cur != NULL)
	{
		if (cur->data == key)
			return 1;
		else if(cur->data < key)
			cur = cur->next;
		else
			return 0;
	}
	return 0;
}

/************************************************************************
Name: insert
Description: Insert a data value into a list.
Input: A root pointer ÕrootÕ of the list and the new data value key.
Output: New root pointer ÕrootÕ of the new list after inserting
*************************************************************************/
struct Node* insert(struct Node* root, int key){
	struct Node *cur = root;
	struct Node *parent = NULL;
	struct Node *x;

	// the original list is empty
	if(root == NULL)
	{
	    x = malloc (sizeof (struct Node));
		x->next = NULL;
		x-> data = key;
		root = x;
		return root;
	}

	// the list is nonempty
	if(cur->data == key)
		return root;
	else if(cur->data < key)
	{
		parent = cur;
		cur = cur->next;
	}

	while(cur != NULL && cur->data < key)
	{
		parent = cur;
		cur = cur->next;
	}

	// the key occurs in the list
	if(cur != NULL && cur->data == key)
	{
		return root;
	}

	// otherwise, key does not occur in the list
	x = malloc (sizeof (struct Node));
	x->next = cur;
	x-> data = key;

	if(parent != NULL)
		parent->next = x;
	else root = x;

	return root;
}

/************************************************************************
Name: delete
Description: Delete a node from a list.
Input: A root pointer ÕrootÕ of the list and value key of the node we need
to delete
Output: New list
*************************************************************************/
struct Node* delete(struct Node* root, int key){
	struct Node *cur = root;
	struct Node *parent = NULL;
	struct Node *nxtparent = NULL;
	struct Node *keynode;
	struct Node *lft;
	struct Node *rgt;
	struct Node *subroot;

	// the original list is empty
	if(root == NULL)
		return root;

	// the list is nonempty
	if(cur->data < key)
	{
		parent = cur;
		cur = cur->next;
	}

	while(cur != NULL && cur->data < key) {
			parent = cur; cur = cur->next;
	}

	// only delete when the key occurs in the list
	keynode = cur;
	if(keynode != NULL && keynode->data == key)
	{
		nxt = keynode->next;
		free(keynode);
		if(parent != NULL)
		{
			parent->next = nxt;
		}
		else
			root = nxt;
	}
	return root;
}
