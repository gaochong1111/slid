// AVL trees

struct Node {
	struct Node *left, *right;
//	struct Node *parent;
	int data;
	signed balance:3;		/* balance factor [-2:+2] */
};


/*
 * search for a node with the desired key
 */
struct Node* search(struct Node* root, int key){
	struct Node *cur = root;
	while (cur != NULL)
	{
		if (cur->data == key)
			return cur;
		else if (cur->data > key)
			cur = cur->left;
		else
			cur = cur->right;
	}
	return NULL;
}

/* Insertion never needs more than 2 rotations */
struct Node * insert(struct Node *root, int key)
{
	struct Node *cur = root;
	struct Node *parent = NULL;
	struct Node *unbalanced = root;
	struct Node *unbparent = NULL;
	struct Node *x;
	struct Node *rgt;
	struct Node *rgtleft;
	struct Node * lft;
	struct Node * lftright;

	//the original tree is empty
	if (root == NULL) {
		x = malloc (sizeof (struct Node));
	    x->left = NULL;
	    x->right = NULL;
	    x->data = key;
	    x ->balance = 0;
		return x;
	}

	// the tree is nonempty

	if(cur->data == key)
	{
		return root;
	}
	else
	{
		if(cur->balance != 0)
		{
			unblananced = cur;
			unbparent = parent;
		}

		if(cur->data > key)
		{
			parent = cur;
			cur = cur->left;
		}
		else
		{
			parent = cur;
			cur = cur->right;
		}
	}

	// search for the key
	while(cur != NULL && cur->data != key)
	{
		if(cur->balance != 0)
		{
			unblananced = cur;
			unbparent = parent;
		}
		parent = cur;
		if(cur->data > key)
			cur = cur->left;
		else
			cur = cur->right;
	}

	// the key occurs in the tree
	if(cur != NULL)
	{
		return root;
	}

	// otherwise, key does not occur in the tree, parent ! = NULL
	x = malloc (sizeof (struct Node));
	x->left = NULL;
	x->right = NULL;
	x-> data = key;
	x->balance = 0;

	if(parent->data > key)
	{
		parent->left = x;
	}
	else
	{
		parent->right = x;
	}

	// update the balance factor top-down, starting from unbalanced
	// originally all the nodes on the path from unbalanced to parent, excluding unbalanced, are balanced
	cur = unbalanced;
	while(cur->data != key){
		if (cur->data > key)
		{
			cur->balance --;
			cur = cur->left;
		}
		else
		{
			cur->balance ++;
			cur = cur->right;
		}
	}

	// rotate if the tree becomes unbalanced after insertion
	if (unbalanced->balance == 2)
	{
		rgt = unbalanced->right;

		if (rgt->balance == 1) {
			// rotate unbalanced left
			unbalanced->right = rgt->left;
			rgt->left = unbalanced;
			unbalanced->balance = 0;
			rgt->balance = 0;
			if(unbparent != NULL)
			{
				if(unbparent->data > key)
				{
					unbparent->left = rgt;
				}
				else
				{
					unbparent->right = rgt;
				}
			}
			else
				root = rgt;
		}
		else
		// in this case, it must be the case that rgt-> balance == -1
		{
			rgtleft = rgt->left;

			// rotate rgt right, then rotate unbalanced left
			rgt->left = rgtleft->right;
			rgtleft->right = rgt;
			unbalanced->right = rgtleft;
			unbalanced->right = rgtleft->left;
			rgtleft->left = unbalanced;

			if (rgtleft->balance == 1){
				unbalanced->balance = -1;
				rgt->balance = 0;
			}
			else if(rgtleft->balance == 0)
			{
				unbalanced->balance = 0;
				rgt->balance = 0;
			}
			else
			{
				unbalanced->balance = 0;
				rgt->balance = 1;
			}

			rgtleft->balance = 0;

			if(unbparent != NULL)
			{
				if(unbparent->data > key)
				{
					unbparent->left = rgtleft;
				}
				else
				{
					unbparent->right = rgtleft;
				}
			}
			else
				root = rgtleft;
		}
	}
	else if (unbalanced->balance == -2)
	{
		lft = unbalanced->left;

		if (lft->balance == -1) {
			//rotate unbalanced right
			unbalanced->left = lft->right;
			lft->right = unbalanced;
			unbalanced->balance = 0;
			lft->balance = 0;
			if(unbparent != NULL)
			{
				if(unbparent->data > key)
				{
					unbparent->left = lft;
				}
				else
				{
					unbparent->right = lft;
				}
			}
			else
				root = lft;
		}
		else
		// in this case, it must be the case that lft->balance == 1
		{
			lftright = lft->right;
			// rotate lft left, then roate unbalanced right
			lft->right = lftright->left;
			lftright->left = lft;
			unbalanced->left = lftright->right;
			lftright->right = unbalanced;

//			  y: unbalance, x: lft,w: lftright
//            if (w->avl_balance == -1)
//               x->avl_balance = 0, y->avl_balance = +1;
//            else if (w->avl_balance == 0)
//               x->avl_balance = y->avl_balance = 0;
//             else /* |w->avl_balance == +1| */
//               x->avl_balance = -1, y->avl_balance = 0;

			if(lftright->balance == 1) {
				unbalance->balance = 0;
				lft->balance = -1;
			}
			else if(lftright->balance == 0)
			{
				unbalance->balance = 0;
				lft->balance = 0;
			}
			else
			{
				unbalance->balance = 1;
				lft->balance = 0;
			}
			lftright->balance = 0;

			if(unbparent != NULL)
			{
				if(unbparent->data > key)
				{
					unbparent->left = lftright;
				}
				else
				{
					unbparent->right = lftright;
				}
			}
			else
				root = lftright;
		}
	}
	/* if after insertion, unbalanced -> balance == +1, -1, then this happens only if originally
	 * all nodes on the path from root to parent have balance == 0, and unbalanced == root.
	*/

	return root;
}

/* Deletion never needs more than 2 rotations */
struct Node* delete (struct Node *root, int key)
{
	struct Node *parent = NULL;
	struct Node *nxtparent;
	struct Node *cur = root;
	struct Node *keynode;
	struct Node *unbalanced = root;
	struct Node *rgt;
	struct Node * lft;
	struct Node *rgtminnode;
	struct Node *rgtleft;
	struct Node *lftright;
	struct Node *unbparent = NULL;
	int keydir;
//	int key_is_left = 0;
//	int unb_is_left = 0;

	//the original tree is empty
	if (root == NULL)
		return root;

	// the tree is nonempty
	if(cur->data != key)
	{
		if(cur->balance != 0)
		{
			unblananced = cur;
			unbparent = parent;
		}

		if(cur->data > key)
		{
			parent = cur;
			cur = cur->left;
		}
		else
		{
			parent = cur;
			cur = cur->right;
		}
	}

	while(cur != NULL && cur->data != key) {
		if(cur->balance != 0)
		{
			unbalanced = cur;
			unbparent = parent;
		}
		if (cur->data > key){
			parent = cur; cur = cur->left;
		}
		else {
			parent = cur; cur = cur->right;
		}
	}

	// if the key is not found in the tree, then do nothing
	if(cur == NULL) return root;

	// delete the keynode, only delete when the key occurs in the bst
	keynode = cur;
	if(keynode->right == NULL)
	{
		if(parent == NULL)
		{
			root = keynode->left;
			free(keynode);
			return root;
		}
		else
		{
			if(parent->data > key)
			{
				parent->left = keynode->left;
				if(keynode->left != NULL)
					keydir = keynode->left->data;
				else
				{
					keydir = parent->data;
					parent->balance ++;
				}
			}
			else
			{
				parent->right = keynode->left;
				if(keynode->left != NULL)
					keydir = keynode->left->data;
				else
				{
					keydir = parent->data;
					parent->balance --;
				}
			}
			free(keynode);
		}
	}
	else{
		/* if the right subtree of the removed node does not have left subtree*/
		rgt = keynode->right;
		if (rgt->left == NULL){
			rgt->left = keynode->left;
			rgt->balance = keynode->balance - 1;
			if(parent == NULL)
			// this implies keynode == root
			{
				root = rgt;
				if(root->balance == 0)
				{
					root->balance--;
					return root;
				}
				else
				{
					unbalanced = root;
					unbparent = NULL;
				}
			}
			else
			{
				if(parent->data > key)
					parent->left = rgt;
				else
					parent->right = rgt;
			}
			keydir = rgt->data;
			free(keynode);
		}
		/* if the right subtree of the removed node has left subtree*/
		else
		{
			if(rgt->balance != 0)
			{
				unbalanced = rgt;
				unbparent = keynode;
			}
			else if(keynode->balance != 0)
			{
				unbalanced = keynode;
				unbparent = parent;
			}
			cur = rgt->left;
			nxtparent = rgt;
			/* search for the smallest node pointed by ÕminÕ in the right subtree*/
			while(cur->left != NULL){
				if(cur->balance != 0)
				{
					unbalanced = cur;
					unbparent = nxtparent;
				}
				nxtparent = cur;
				cur = cur->left;
			}
			// exchange removed node with the smallest node
			if(cur->right != NULL)
				keydir = cur->right->data;
			else
			{
				keydir = nxtparent->data;
				nxtparent->balance++;
			}
			nxtparent->left = cur->right;
			cur->left = keynode->left;
			cur->right = rgt;
			cur->balance = keynode->balance;
			if(parent == NULL)
				root = cur;
			else
			{
				if(parent->data > key)
					parent->left = cur;
				else
					parent->right = cur;
			}
			if(unbalanced == keynode)
			{
				unbalanced = cur;
				unbparent = parent;
			}
			free(keynode);
		}
	}

	// update the balance factor top-down, starting from unbalanced
	// originally all the nodes on the path from unbalanced to parent, excluding unbalanced, are balanced
	cur = unbalanced;
	while(cur->data != keydir){
		if (cur->data > keydir)
		{
			cur->balance ++;
			cur = cur->left;
		}
		else
		{
			cur->balance --;
			cur = cur->right;
		}
	}

	// rotate if the tree becomes unbalanced after deletion
	if (unbalanced->balance == 2)
	{
		rgt = unbalanced->right;

		if (rgt->balance == 1) {
			// rotate unbalanced left
			unbalanced->right = rgt->left;
			rgt->left = unbalanced;
			unbalanced->balance = 0;
			rgt->balance = 0;
			if(unbparent != NULL)
			{
				if(unbparent->data > unbalanced->data)
				{
					unbparent->left = rgt;
				}
				else
				{
					unbparent->right = rgt;
				}
			}
			else
				root = rgt;
		}
		else
		// in this case, it must be the case that rgt-> balance == -1
		{
			rgtleft = rgt->left;

			// rotate rgt right, then rotate unbalanced left
			rgt->left = rgtleft->right;
			rgtleft->right = rgt;
			unbalanced->right = rgtleft;
			unbalanced->right = rgtleft->left;
			rgtleft->left = unbalanced;

			rgtleft->balance = 0;

			if (rgtleft->balance == 1){
				unbalanced->balance = -1;
				rgt->balance = 0;
			}
			else if(rgtleft->balance == 0)
			{
				unbalanced->balance = 0;
				rgt->balance = 0;
			}
			else
			{
				unbalanced->balance = 0;
				rgt->balance = 1;
			}
			if(unbparent != NULL)
			{
				if(unbparent->data > unbalanced->data)
				{
					unbparent->left = rgtleft;
				}
				else
				{
					unbparent->right = rgtleft;
				}
			}
			else
				root = rgtleft;
		}
	}
	else if (unbalanced->balance == -2)
	{
		lft = unbalanced->left;

		if (lft->balance == -1) {
			//rotate unbalanced right
			unbalanced->left = lft->right;
			lft->right = unbalanced;
			unbalanced->balance = 0;
			lft->balance = 0;
			if(unbparent != NULL)
			{
				if(unbparent->data > unbalanced->data)
				{
					unbparent->left = lft;
				}
				else
				{
					unbparent->right = lft;
				}
			}
			else
				root = lft;
		}
		else
		// in this case, it must be the case that lft->balance == 1
		{
			lftright = lft->right;
			// rotate lft left, then roate unbalanced right
			lft->right = lftright->left;
			lftright->left = lft;
			unbalanced->left = lftright->right;
			lftright->right = unbalanced;

			lftright->balance = 0;
			if(lftright->balance == 1) {
				unbalanced->balance = 0;
				lft->balance = -1;
			}
			else if(lftright->balance == 0)
			{
				unbalanced->balance = 0;
				lft->balance = 0;
			}
			else
			{
				unbalanced->balance = 1;
				lft->balance = 0;
			}

			if(unbparent != NULL)
			{
				if(unbparent->data > unbalanced->data)
				{
					unbparent->left = lftright;
				}
				else
				{
					unbparent->right = lftright;
				}
			}
			else
				root = lftright;
		}
	}
	/* if after deletion, unbalanced -> balance == +1, -1, then this happens only if originally
	 * all nodes on the path from root to parent have balance == 0, and unbalanced == root.
	*/
	return root;
}
