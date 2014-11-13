/  /*----------------------------------------------------------------*\
//  |   Concrete Template : Partial_Map_Kernel_7
//  |   Written By: Brett Koenig
//  |  This implements functions for a partial map structure
//  \*----------------------------------------------------------------*/

#ifndef CT_PARTIAL_MAP_KERNEL_7
#define CT_PARTIAL_MAP_KERNEL_7 1

///---------------------------------------------------------------------
/// Global Context -----------------------------------------------------
///---------------------------------------------------------------------

#include "AT/Partial_Map/Kernel.h"
/*!
    #include "AT/General/Is_Equal_To.h"
    #include "AT/General/Are_In_Order.h"
!*/
#include "CT/Binary_Tree/Kernel_1a.h"

///---------------------------------------------------------------------
/// Interface ----------------------------------------------------------
///---------------------------------------------------------------------

concrete_template <
        concrete_instance class D_Item,
        /*!
            implements
                abstract_instance General_Is_Equal_To <D_Item, D_Item>
        !*/
        concrete_instance class R_Item,
        concrete_instance utility_class D_Item_Are_In_Order,
        /*!
            implements
                abstract_instance General_Are_In_Order <D_Item>
        !*/
        concrete_instance class D_R_Pair =
      Record <
        D_Item, 
        R_Item
                >,
        concrete_instance class Binary_Tree_Of_D_R_Pair =
            Binary_Tree_Kernel_1a <D_R_Pair>,
        concrete_instance class Rep =
            Representation <
        Integer,
        D_R_Pair,
        Binary_Tree_Of_D_R_Pair
    >
    >
class Partial_Map_Kernel_7 :
    implements
        abstract_instance Partial_Map_Kernel <
                D_Item, 
                R_Item
            >,
    encapsulates
        concrete_instance Rep
{

private:

    rep_field_name (Rep, 0, Integer, number_of_pairs);
    rep_field_name (Rep, 1, D_R_Pair, cache);
    rep_field_name (Rep, 2, Binary_Tree_Of_D_R_Pair, tree_of_pairs);

    field_name (D_R_Pair, 0, D_Item, d_item);
    field_name (D_R_Pair, 1, R_Item, r_item);  
    /*!
  math subtype TREE_ITEM is (
    d_item: D_Item,
    r_item: R_Item
      )

  math definition ELEMENTS (
    t: binary tree of TREE_ITEM
      ): finite set of TREE_ITEM satisfies
      if t = empty_tree
      then ELEMENTS (t) = {}
      else there exists root: TREE_ITEM
            left, right: binary tree of TREE_ITEM
        (t = compose (root, left, right) and
         ELEMENTS (t) = {root} union
       ELEMENTS (left) union ELEMENTS (right))

  math definition D_ELEMENTS (
    t: binary tree of TREE_ITEM
      ): finite set of D_ITEM satisfies
      if t = empty_tree
      then D_ELEMENTS (t) = {}
      else there exists root: TREE_ITEM
            left, right: binary tree of TREE_ITEM
        (t = compose (root, left, right) and
         D_ELEMENTS (t) = {root.d_item} union
       D_ELEMENTS (left) union D_ELEMENTS (right))

  math definition IS_BST_ORDERED (
    t: binary tree of TREE_ITEM
      ): boolean satisfies
      if t = empty_tree
      then IS_BST_ORDERED (t) = true
      else there exists root: TREE_ITEM
            left, right: binary tree of TREE_ITEM
        (t = compose (root, left, right) and
         IS_BST_ORDERED (t) =
       IS_BST_ORDERED (left)  and
       IS_BST_ORDERED (right)  and
       for all d: D_Item
           where (d is in D_ELEMENTS (left))
               (not ARE_IN_ORDER (root.d_item, d))  and
       for all d: D_Item
           where (d is in D_ELEMENTS (right))
               (ARE_IN_ORDER (root.d_item, d)))

  math definition TREE_CONV (
    t: binary tree of TREE_ITEM
      ): boolean is
      SIZE (t) = |D_ELEMENTS (t)|  and
      IS_BST_ORDERED (t)

  math definition CONV (
    n: integer,
    c: TREE_ITEM,
    t: binary tree of TREE_ITEM
      ): boolean is
      n >= 0  and
      TREE_CONV (t)  and
      (if n = 0
       then SIZE (t) = 0
       else (SIZE (t) = n - 1  and
             c.d_item is not in D_ELEMENTS (t)))

  math definition CORR (
    n: integer,
    c: TREE_ITEM,
    t: binary tree of TREE_ITEM
      ): finite set of TREE_ITEM satisfies
      if n = 0
      then CORR (n, c, t) = {}
      else CORR (n, c, t) = {c} union ELEMENTS (t)

  convention
      CONV (self.number_of_pairs, self.cache, self.tree_of_pairs)
      
  correspondence
      self = CORR (self.number_of_pairs, self.cache,
       self.tree_of_pairs)
    !*/

    local_procedure_body Add_Pair_To_Tree (
            alters Binary_Tree_Of_D_R_Pair& t,
            consumes D_R_Pair& pair
        )
    /*!
   requires
       TREE_CONV (t)  and
       pair.d_item is not in D_ELEMENTS (t)
   ensures
       TREE_CONV (t)  and
       ELEMENTS (t) = ELEMENTS (#t) union {pair}
   decreases
       SIZE (t)
    !*/
    {
  if (t.Size () == 0)
  {
      object catalyst Binary_Tree_Of_D_R_Pair empty_left, empty_right;

      t.Compose (pair, empty_left, empty_right);
  }
  else
  {
      object catalyst D_R_Pair root;
      object catalyst Binary_Tree_Of_D_R_Pair left, right;

      t.Decompose (root, left, right);

      if (D_Item_Are_In_Order::Are_In_Order (root[d_item], pair[d_item]))
      {
    Add_Pair_To_Tree (right, pair);
      }
      else
      {
    Add_Pair_To_Tree (left, pair);
      }

      t.Compose (root, left, right);
  }    
    }

    local_procedure_body Remove_Pair_From_Tree (
            alters Binary_Tree_Of_D_R_Pair& t,
            preserves D_Item& d,
            produces D_R_Pair& pair
        )
    /*!
   requires
       TREE_CONV (t)  and
       d is in D_ELEMENTS (t)
   ensures
       TREE_CONV (t)  and
       pair is in ELEMENTS (#t)  and
       ELEMENTS (t) = ELEMENTS (#t) - {pair}  and
       pair.d_item = d
   decreases
       SIZE (t)
    !*/
    {
  object D_R_Pair root, small;
  object Binary_Tree_Of_D_R_Pair left, right;
  
  if(d.Is_Equal_To (t[current][d_item]))
  {
      t.Decompose(root, left, right);
      if(t.Size()>0)
      {
    Remove_Smallest_Pair_From_Tree(right, small);
    t.Compose(small, left, right);
      }
      pair &= root;
  }
  else if(D_Item_Are_In_Order::Are_In_Order (d, t[current][d_item]))
  {
      t.Decompose(root, left, right);
      Remove_Pair_From_Tree(left, d, pair);
  }
  else if(!D_Item_Are_In_Order::Are_In_Order (d, t[current][d_item]))
  {
      t.Decompose(root, left, right);
      Remove_Pair_From_Tree(right, d, pair);      
  } 
    }

    local_procedure_body Remove_Smallest_Pair_From_Tree (
            alters Binary_Tree_Of_D_R_Pair& t,
            produces D_R_Pair& small_pair
        )
    /*!
   requires
       TREE_CONV (t)  and
       t /= empty_tree
   ensures

   TREE_CONV (t)  and
       small_pair is in ELEMENTS (#t)  and
       ELEMENTS (t) = ELEMENTS (#t) - {small_pair}  and
       for all d: D_Item
           where (d is in D_ELEMENTS (t))
         (ARE_IN_ORDER (small_pair.d_item, d))
   decreases
       SIZE (t)
    !*/
    {
  object Binary_Tree_Of_D_R_Pair left, right, blank1, blank2;
  object D_R_Pair root;
  t.Decompose(root, left, right);
  if(left.Size()==0){
      small_pair &=  root;
      t &= right;
  }
  else{
      Remove_Smallest_Pair_From_Tree(left, small_pair);
      t.Compose(root, left, right);
  }
    }

    local_function_body Boolean Is_In_Tree (
            preserves Binary_Tree_Of_D_R_Pair& t,
            preserves D_Item& d
        )
    /*!
   requires
       TREE_CONV (t)
   ensures
       Is_In_Tree = (d is in D_ELEMENTS (t))
   decreases
       SIZE (t)
    !*/
    {
  object Boolean In_Tree;
  if(t.Size() > 0)
  {
      object D_R_Pair root;
      object Binary_Tree_Of_D_R_Pair left, right;
      t.Decompose(root,left,right);
      if(root[d_item].Is_Equal_To(d))
      {
    In_Tree= true;
      }
      else
      {
    Is_In_Tree(left, d);
    Is_In_Tree(right, d);
      }
      t.Compose(root,left,right);
  }
  return In_Tree;
    }
    

public:

    standard_concrete_operations (Partial_Map_Kernel_7);

    procedure_body Define (
            consumes D_Item& d,
            consumes R_Item& r
        )
    {
  if (self[number_of_pairs] == 0)
  {
      // Put (#d,#r) into cache, which is currently unoccupied

      self[cache][d_item] &= d;
      self[cache][r_item] &= r;

      // Consume d and r

      d.Clear ();
      r.Clear ();
  }
  else
  {
      // Put (#d,#r) into tree, since cache is currently occupied

      object catalyst D_R_Pair pair;
      pair[d_item] &= d;
      pair[r_item] &= r;
      Add_Pair_To_Tree(self[tree_of_pairs], pair);
  }

  // Update number of pairs
  
  self[number_of_pairs]++;
    }

    procedure_body Undefine (
            preserves D_Item& d,
            produces D_Item& d_copy,
            produces R_Item& r
        )
    {
  if(Is_Defined(d))
  {
      if((d.Is_Equal_To(self[cache][d_item])))
      {
    d_copy &= self[cache][d_item];
    r &= self[cache][r_item];   
      }
      else
      {
    object D_R_Pair pair;
    Remove_Pair_From_Tree(self[tree_of_pairs], d, pair);
    d_copy &= pair[d_item];
    r &= pair[r_item];
      }
      self[number_of_pairs]--;
  }
    }

    procedure_body Undefine_Any (
            produces D_Item& d,
            produces R_Item& r
        )
    {
  object D_R_Pair small;
  Remove_Smallest_Pair_From_Tree(self[tree_of_pairs], small);
  small[d_item] &= d;
  small[r_item] &= r;
  self[number_of_pairs]--;  
    }

    function_body Boolean Is_Defined (
            preserves D_Item& d
        )
    {
  object Boolean foo;
  if(d.Is_Equal_To(self[cache][d_item]))
  {
      foo = true;
  }
  else if(Is_In_Tree(self[tree_of_pairs],d))
  {
      foo = true;
  }
  else
  {
      foo = false;
  }
  return foo;
    }

    function_body R_Item& operator [] (
            preserves D_Item& d
        )
    {
  if(d.Is_Equal_To(self[cache][d_item]))
  {
      return self[cache][r_item];
  }
  else
  {
      object D_Item d2, d_copy;
      object R_Item r, r_und;
      self[cache][d_item] &= d2;
      self[cache][r_item] &= r;
      Define(d2,r);
      Undefine(d, d_copy, r_und);
      self[cache][d_item] &= d_copy;
      self[cache][r_item] &= r_und;
      return self[cache][r_item];
  }
    }

    function_body Integer Size ()
    {
  return self[number_of_pairs];    
    }

};

#endif // CT_PARTIAL_MAP_KERNEL_7

