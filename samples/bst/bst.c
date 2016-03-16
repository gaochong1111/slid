//************************************************************************
//****** Binary Search Trees
//************************************************************************

/************************************************************************
Name: Node
Description: Structure of a node in a binary search tree
*************************************************************************/
struct Node
{
  struct Node *left;            // Left pointer field
  struct Node *right;           // Right pointer field
  int data;                     // Data field
};


/************************************************************************
Name: search
Description: Search a data value in a binary search tree.
Input: A root pointer ÕrootÕ of the tree and data value v.
Output: true if the data value is found, otherwise false.
*************************************************************************/

struct Node *
search (struct Node *root, int key)
{
  Node *cur;
  cur = root;
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

/************************************************************************
Name: insert
Description: Insert a data value into a binary search tree.
Input: A root pointer ÕrootÕ of the tree and the new data value ÕnewÕ.
Output: New root pointer ÕrootÕ of the new tree after inserting
*************************************************************************/
struct Node *
insert (struct Node *root, int key)
{
  Node *cur;
  if (root == NULL)
    {
      malloc x;
      x->left = NULL;
      x->right = NULL;
      x->data = key;
      return x;
    }
  cur = root;
  while (cur->data != key)
    if (cur->data < key)
      if (cur->right != NULL)
        cur = cur->right;
      else
        {
          malloc x;
          x->left = NULL;
          x->right = NULL;
          x->data = key;
          cur->right = x;
        }
    else if (cur->left != NULL)
      cur = cur->left;
    else
      {
        malloc x;
        x->left = NULL;
        x->right = NULL;
        x->data = key;
        cur->left = x;
      }
  return root;
}

/************************************************************************
Name: leftRotate
Description: Left rotate a binary search tree.
Input: A root pointer ÕrootÕ of the tree.
Output: New root pointer ÕrootÕ of the new tree after left rotating
*************************************************************************/
struct Node *
leftRotate (struct Node *root)
{
  if (root->left != NULL)
    {
      struct Node *r = root->left;
      root->left = r->right;
      r->right = root;
      return r;
    }
  return root;
}

/************************************************************************
Name: rightRotate
Description: Right rotate a binary search tree.
Input: A root pointer ÕrootÕ of the tree.
Output: New root pointer ÕrootÕ of the new tree after right rotating
*************************************************************************/
struct Node *
rightRotate (struct Node *root)
{
  if (root->right != NULL)
    {
      struct Node *r = root->right;
      root->right = r->left;
      r->left = root;
      return r;
    }
  return root;
}

/************************************************************************
Name: delete
Description: Delete a node from a binary search tree.
Input: A root pointer ÕrootÕ of the tree and value key of the node we need
to delete
Output: New binary search tree
*************************************************************************/
struct Node *
delete (struct Node *root, int key)
{
  struct Node *tmp = NULL;
  struct Node *cur = root;
  struct Node *parent = NULL;
  // search for the node with value key
  if (cur->data == key)
    {
      return deleteroot (root);
    }
  else if (cur->data > key)
    {
      parent = cur;
      cur = cur->left;
    }
  else
    {
      parent = cur;
      cur = cur->right;
    }

  while (cur != NULL && cur->data != key)
    {
      if (cur->data > key)
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

  // only delete when the key occurs in the bst
  if (cur != NULL)
    {
      //cur is not the root
      if (parent->data > key)
        {
          tmp = deleteroot (cur);
          parent->left = tmp;
        }
      else
        {
          tmp = deleteroot (cur);
          parent->right = tmp;
        }
    }
  return root;
}

struct Node *
deleteroot (struct Node *root)
{
  struct Node *right = NULL;
  struct Node *cur = root;
  struct Node *parent = NULL;
  // if the root does not have right subtree
  if (root->right == NULL)
    {
      cur = cur->left;
      free (root);
    }
  else
    {
      /* if the right subtree of the removed node does not have left subtree */
      if (root->right->left == NULL)
        {
          cur = cur->right;
          cur->left = root->left;
          free (root);
        }
      /* if the right subtree of the removed node has left subtree */
      else
        {
          right = root->right;
          cur = root->right->left;
          parent = right;
          /* search for the smallest node pointed by ÕminÕ in the right subtree */
          while (cur->left != NULL)
            {
              parent = cur;
              cur = cur->left;
            }
          // exchange removed node with the smallest node
          parent->left = cur->right;
          cur->left = root->left;
          cur->right = right;
          free (root);
        }
    }
  return cur;
}
