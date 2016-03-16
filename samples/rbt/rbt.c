struct Node {
	struct Node *left, *right;
	int data;
	enum color color;
};

struct Node * insert(struct Node *root, int key)
{
	struct Node *cur = root;
	struct Node *parent = NULL, *grandpa = NULL, *ggrandpa = NULL;
	struct Node *uncle;
	struct Node *cusnode = root; // the node where the top-down update of the colors starts
	struct Node *cusparent = NULL; // the parent of usnode
	struct Node *x;
	int is_even = 0;

	//the original tree is empty
	if (root == NULL) {
		x = malloc (sizeof (struct Node));
	    x->left = NULL;
	    x->right = NULL;
	    x->data = key;
	    x ->color = 0; // 0: red, 1: black
		return x;
	}

	// the tree is nonempty

	if(cur->data == key)
		return root;

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
	is_even = 1;

	while(cur != NULL && cur->data != key)
	{
		parent = cur;

		if(cur->data > key)
			cur = cur->left;
		else
			cur = cur->right;

		if(is_even == 0)
			is_even = 1;
		else
			is_even = 0;
	}
	// the key occurs in the tree
	if(cur != NULL)
		return root;

	// otherwise, key does not occur in the tree
	x = malloc (sizeof (struct Node));
	x->left = NULL;
	x->right = NULL;
	x-> data = key;
	x->color = 0;

	if(parent->data > key)
		parent->left = x;
	else
		parent->right = x;

	if(parent == root)
		return root;

	// rebalance the red-black tree
	// at first determine the cusnode by traversing top-down
	if(is_even == 0)
	{
		ggrandpa = NULL;
		grandpa  = root;
	}
	else
	{
		ggrandpa = root;
		if(root->data > key)
			grandpa = root->left;
		else
			grandpa = root->right;
	}

	// since parent != root, the subtree rooted at grandpa has depth at least two
	if(grandpa->data > key)
	{
		parent = grandpa->left;
		uncle = grandpa->right;
	}
	else
	{
		parent = grandpa->right;
		uncle = grandpa->left;
	}
	if(parent->data > key)
		cur = parent->left;
	else
		cur = parent->right;
	cusnode = grandpa;
	cusparent = ggrandpa;

	// determine the cusnode
	is_even = 0;
	while(cur != NULL)
	{
		if(is_even == 0)
		{
			if(parent->color == 1 || uncle == NULL || uncle->color == 1)
			{
				cusnode = grandpa;
				cusparent = ggrandpa;
			}
		}

		ggrandpa = grandpa;
		grandpa = parent;
		if(grandpa->data > key)
			uncle = grandpa->right;
		else
			uncle = grandpa->left;

		parent = cur;

		if(parent->data > key)
			cur = parent->left;
		else
			cur = parent->right;

		if(is_even == 0)
			is_even = 1;
		else
			is_even = 0;
	}

	// update the color top-down, starting from cusnode
	// in the original tree all the even-position nodes on the path from cusnode to the grandpa of x,
	// excluding cusnode, have the red color and their uncles are red

	grandpa = cusnode;
	if (grandpa->data > key)
		parent = grandpa->left;
	else
		parent = grandpa->right;
	if (parent->data > key)
		cur = parent->left;
	else
		cur = parent->right;
	grandpa = cur;

	while(grandpa->data != key)
	{
		if (grandpa->data > key)
		{
			parent = grandpa->left;
			uncle = grandpa ->right;
		}
		else
		{
			parent = grandpa->right;
			uncle = grandpa->left;
		}
		if (parent->data > key)
			cur = parent->left;
		else
			cur = parent->right;

		grandpa->color = 0; // red
		parent->color = 1; // black
		uncle->color = 1; // black

		grandpa = cur;
	}

	// apply the rotations if necessary
	if (cusnode->data > key)
	{
		parent = cusnode->left;
		uncle = cusnode->right;
		if (parent->data > key)
			cur = parent->left;
		else
			cur = parent->right;

		// this happens only if cusnode = root or cusparent = root
		if (parent->color == 0 && uncle != NULL && uncle->color == 0)
		{
			if(cusparent != NULL)
			{
				cusnode->color = 0;
				parent->color = 1;
				uncle->color = 1;
			}
			else
			{
				cusnode->color = 1;
				parent->color = 1;
				uncle->color = 1;
			}
		}
		else if(parent->color == 0) // in this case, uncle == NULL or uncle is black
		{
			if (parent->data < key)
			{
				// rotate left around parent, then rotate right around cusnode
				parent->right = cur -> left;
				cur -> left = parent;
				cusnode->left = cur->right;
				cur->right = cusnode;
				cur->color = 1;
				cusnode->color = 0;
				if(cusparent != NULL)
				{
					if(cusparent->data > key)
						cusparent->left = cur;
					else
						cusparent->right = cur;
				}
				else
					root = cur;
			}
			else
			{
				// rotate right around cusnode
				parent->color = 1;
				cusnode->color = 0;
				cusnode->left = parent->right;
				parent->right = cusnode;
				if(cusparent != NULL)
				{
					if(cusparent->data > key)
						cusparent->left = parent;
					else
						cusparent->right = parent;
				}
				else
					root = parent;
			}
		}
	}
	else
	{
		parent = cusnode->right;
		uncle = cusnode->left;
		if (parent->data > key)
			cur = parent->left;
		else
			cur = parent->right;

		// this happens only if cusnode = root or cusparent = root
		if (parent->color == 0 && uncle != NULL && uncle->color == 0)
		{
			if(cusparent != NULL)
			{
				cusnode->color = 0;
				parent->color = 1;
				uncle->color = 1;
			}
			else
			{
				cusnode->color = 1;
				parent->color = 1;
				uncle->color = 1;
			}
		}
		else if(parent->color == 0)
		{
			if (parent->data > key)
			{
				// rotate right around parent, then rotate left around cusnode
				cusnode->right = cur->left;
				cur->left = cusnode;
				parent->left = cur->right;
				cur->right = parent;
				cur->color = 1;
				cusnode->color = 0;
				if(cusparent != NULL)
				{
					if (cusparent->data > key)
						cusparent->left = cur;
					else
						cusparent->right = cur;
				}
				else
					root = cur;
			}
			else
			{
				parent->color = 1;
				cusnode->color = 0;
				// rotate left around cusnode
				cusnode->right = parent->left;
				parent->left = cusnode;
				if(cusparent != NULL)
				{
					if (cusparent->data > key)
						cusparent->left = parent;
					else
						cusparent->right = parent;
				}
				else
					root = parent;
			}
		}
	}
	return root;
}

struct Node* delete(struct Node *root, int key)
{
	struct Node *parent = get_parent(node);
	struct Node *left = node->left;
	struct Node *right = node->right;
	struct Node *next;
	enum rb_color color;

	if (node == tree->first)
		tree->first = rbtree_next(node);
	if (node == tree->last)
		tree->last = rbtree_prev(node);

	if (!left)
		next = right;
	else if (!right)
		next = left;
	else
		next = get_first(right);

	if (parent)
		set_child(next, parent, parent->left == node);
	else
		tree->root = next;

	if (left && right) {
		color = get_color(next);
		set_color(get_color(node), next);

		next->left = left;
		set_parent(next, left);

		if (next != right) {
			parent = get_parent(next);
			set_parent(get_parent(node), next);

			node = next->right;
			parent->left = node;

			next->right = right;
			set_parent(next, right);
		} else {
			set_parent(parent, next);
			parent = next;
			node = next->right;
		}
	} else {
		color = get_color(node);
		node = next;
	}
	/*
	 * 'node' is now the sole successor's child and 'parent' its
	 * new parent (since the successor can have been moved).
	 */
	if (node)
		set_parent(parent, node);

	/*
	 * The 'easy' cases.
	 */
	if (color == RB_RED)
		return;
	if (node && is_red(node)) {
		set_color(RB_BLACK, node);
		return;
	}

	do {
		if (node == tree->root)
			break;

		if (node == parent->left) {
			struct Node *sibling = parent->right;

			if (is_red(sibling)) {
				set_color(RB_BLACK, sibling);
				set_color(RB_RED, parent);
				rotate_left(parent, tree);
				sibling = parent->right;
			}
			if ((!sibling->left  || is_black(sibling->left)) &&
			    (!sibling->right || is_black(sibling->right))) {
				set_color(RB_RED, sibling);
				node = parent;
				parent = get_parent(parent);
				continue;
			}
			if (!sibling->right || is_black(sibling->right)) {
				set_color(RB_BLACK, sibling->left);
				set_color(RB_RED, sibling);
				rotate_right(sibling, tree);
				sibling = parent->right;
			}
			set_color(get_color(parent), sibling);
			set_color(RB_BLACK, parent);
			set_color(RB_BLACK, sibling->right);
			rotate_left(parent, tree);
			node = tree->root;
			break;
		} else {
			struct Node *sibling = parent->left;

			if (is_red(sibling)) {
				set_color(RB_BLACK, sibling);
				set_color(RB_RED, parent);
				rotate_right(parent, tree);
				sibling = parent->left;
			}
			if ((!sibling->left  || is_black(sibling->left)) &&
			    (!sibling->right || is_black(sibling->right))) {
				set_color(RB_RED, sibling);
				node = parent;
				parent = get_parent(parent);
				continue;
			}
			if (!sibling->left || is_black(sibling->left)) {
				set_color(RB_BLACK, sibling->right);
				set_color(RB_RED, sibling);
				rotate_left(sibling, tree);
				sibling = parent->left;
			}
			set_color(get_color(parent), sibling);
			set_color(RB_BLACK, parent);
			set_color(RB_BLACK, sibling->left);
			rotate_right(parent, tree);
			node = tree->root;
			break;
		}
	} while (is_black(node));

	if (node)
		set_color(RB_BLACK, node);
}
