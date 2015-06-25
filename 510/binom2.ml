(* This programming assignment is to implement "Binomial Queues",
 an efficient data structure for priority queues with the following
 properties:
  INSERT is efficient
  DELETE THE MAXIMUM is efficient
  JOIN is efficient
  ALL OPERATIONS ARE NONDESTRUCTIVE, so that "revert to a previous queue"
   is constant-time
  Binomial Queues are described in Section 9.7 of, 
     Sedgewick, Robert.
     Algorithms, Third Edition, in Java, Parts 1-4: Fundamentals, 
     Data Structures, Sorting, and Searching. 
     Addison-Wesley, 2002.
  The explanations and pictures there will be very helpful in understanding
  this assignment.
  You will also find some Java code there.  You may use it for reference,
  but it's not written in a style that's natural for ML, and you would do
  better to rely on the pictures and picture-captions.
*)

(* An "N-node power-of-2-heap" is a binary tree with the following properties:
  1.  The key at a node is GREATER OR EQUAL TO the all the keys in the LEFT
     subtree of that node.
  2.  The LEFT child of the root node is a complete balanced binary tree
     containing N-1 nodes.
  3.  The RIGHT child of the root is empty.
*)

type 'a tree = Node of 'a * 'a tree * 'a tree | Leaf;;
type key = int

(* We will use the type "key" for the values in the heaps, but we 
   will use the type "int" to describe the size or depth of the heaps.
*)

(* Problem 1. implement a function "pow2heap" that checks whether 
   a tree is a power-of-2-heap. If t is a power-of-2-heap with 2^n nodes, 
    then (pow2heap n t) returns unit.
   Otherwise, (pow2heap n t) raises the exception (IllFormed(n,t)).
*)

exception IllFormed of (int * key tree);;

let root (t : key tree) : int = 
    match t with Leaf -> raise (IllFormed (0, t))
    | Node (hd, lc, rc) -> hd;;

let left (t : key tree) : key tree = 
    match t with Leaf -> raise (IllFormed (0, t))
    | Node (_, lc, _) -> lc;;

(* clheap: complele left heap ordered *)
let rec clheap (t : key tree) : bool = 
    match t with Leaf -> true
    | Node(hd, Leaf, Leaf) -> true
    | Node(hd, Leaf, _) -> false
    | Node(hd, _, Leaf) -> false
    | Node(hd, lc, rc) -> 
        if hd >= (root lc) && clheap lc && clheap rc 
        then true else false;;

let rec depth (t : key tree) : int =
    match t with Leaf -> 0
    | Node(hd, lc, rc) -> 1 + (depth lc);;

let pow2heap (n: int) (t: key tree) : unit = 
    match t with Leaf -> if n = 0 then () else raise (IllFormed (n, t))
    | Node(hd, Leaf, Leaf) -> ()
    | Node(hd, lc, rc) -> 
        if (clheap lc) && rc = Leaf && (depth lc) = n 
        then () else raise (IllFormed (n, t));;

(* A priority queue (using the binomial queues data structure)
   is a list of trees.  
   The i'th element of the list is either Leaf or it is a
   power-of-2-heap with exactly 2^i nodes.
*)

type 'a priqueue = 'a tree list;;

let emptyQ : 'a priqueue = [];;

(* Problem 2.  Implement a function     priq: key priqueue -> unit
  that checks whether a priority queue is well formed.
  If it is not well formed, raise the exception IllFormed(n,t)
  to complain about the specific list element that is bad; otherwise
  return ().
*)

(* let rec formed (n : int) (q : key priqueue) : unit =
    match q with [] -> () 
    | hd :: tl -> if (pow2heap n hd) = () 
        then formed (n+1) tl 
        else raise (IllFormed (n, hd));; *)

let rec priq (q : key priqueue) : unit =
  match q with [] -> ()
  | hd :: tl -> if hd = Leaf
	then priq tl
	else let n = (depth hd) - 1 in
	  if (pow2heap n hd) = () 
	      then priq tl
	      else raise (IllFormed (n, hd));;

(* let priq (q: key priqueue) : unit = formed 0 q;; *)

exception SmashError;;

(* We join two power-of-two heaps (if they are the same size) by putting 
   the larger of the roots at the root of the new tree, with that 
   root's LEFT subtree as the RIGHT subtree of the other original root.
*)

(* Problem 3.  Implement a function smash: key tree -> key tree -> key tree
   that joins two nonempty power-of-two heaps, if they are the same size.
   If they are not the same size, then "smash" can either return
   an ill-formed tree or raise SmashError, as you wish.
*)

let smash  (t : key tree) (u : key tree) : key tree = 
    let lt = depth (left t) in
    let lu = depth (left t) in 
    if lt = lu && pow2heap lt t = () && pow2heap lu u = () 
    then
        if (root t) < (root u) 
        then Node ((root u), Node (root t, left t, left u), Leaf)
        else Node ((root t), Node (root u, left u, left t), Leaf)
    else raise SmashError;;
     
(* Problem 3a.  Demonstrate a test case.  Do more than one if you
   want to save time later by having debugged this part early.  *)
let tree0 : key tree = Node (11, Node(9, Node(8, Leaf, Leaf), Node(10, Leaf, Leaf)), Leaf);;
let test_tree0 = pow2heap 2 tree0;;
let tree1 : key tree = Node (9, Node (7, Node(6, Leaf, Leaf), Node(5, Leaf, Leaf)), Leaf);; (* fix me *)
let test_tree1 = pow2heap 2 tree1;;
let tree2 : key tree = Node (11, Node (10, Node(7, Leaf, Leaf), Node(6, Leaf, Leaf)), Leaf);; (* fix me *)
let test_tree2 = pow2heap 2 tree2;;
let tree12 = smash tree1 tree2;;
let test_tree12 = pow2heap 3 tree12;;
let tree3 : key tree = Node (1, Leaf, Leaf);;
let tree4 : key tree = Node (2, Leaf, Leaf);;
let tree34 = smash tree3 tree4;;
let test_tree34 = pow2heap 1 tree34;;

(* The "carry" function merges a list-of-trees with a tree,
  as follows.  Let q be a list where the
   i'th element is either Leaf or a power-of-2-heap of size 2^(n+i).
   Let t be either a Leaf or a power-of-2-heap of size 2^n.
   Then   (carry q t) performs the operation that Sedgewick describes
   as "similar to incrementing a binary number": it smashes
   t with the first element in q, and smashes the result with
   the second element in q, and so on, until it gets to a Leaf
   (or the end of q).
  To insert a key into a priority queue, simply "carry" the key
  in from the small end of the list.
  Problem 4.  Implement the carry function and the insert function.
*)

let rec carry (q: key priqueue) (t: key tree) : key priqueue = 
    let ind = (depth t) - 1 in
    if t = Leaf then q
    else
        match q with [] -> [t]
        | hd :: tl -> if (depth hd) - 1 = ind
            then carry tl (smash hd t)
            else hd :: (carry tl t);;

let insert (q: key priqueue) (x: key) : key priqueue = carry q (Node(x, Leaf, Leaf));;

(* Problem 4b.  Do a test case.  *)

let queue0 = List.fold_left insert emptyQ [3;2];;
let test_queue0 = priq queue0;;
let queue1 = List.fold_left insert emptyQ [3;1;4;1;5;9;2;3;5];;
let test_queue1 = priq queue1;;

(* The maximum element of a binomial queue, implemented as a list
   of power-of-2 heaps, is the max element of any of those heaps.
   The max element of those heaps is at the root (because the
   right child is always a Leaf).
Problem 5.  Implement a function to find the max element of a priqueue.
  It should raise Empty if q has no elements.
  Demonstrate this on queue1.
*)

exception Empty;;

let rec find_max (q: key priqueue) : key = 
  match q with [] -> raise Empty
  | hd :: [] -> root hd
  | hd :: tl -> if (root hd > root (List.hd tl)) 
       then find_max (hd :: (List.tl tl))
	else find_max tl;;

(* Two priority queues may be joined together by a process that
   Sedgewick says "mimics the binary addition" function.
   This is shown in Figure 9.20.   You should be able to implement
   this WITHOUT using any numbers (except the key elements themselves);
   certainly the "bits" hack that Sedgewick uses in Program 9.16 is
   not necessary, since you can use ML's powerful pattern-matching
   facility.
Problem 6.  Implement the join function on priority queues.
   Note that p and q don't have to be same length.
   This join has a "carry in" argument (c).
*)

let rec join (p: key priqueue) (q: key priqueue) (c: key tree) : key priqueue =
  match q with [] -> carry p c
  | hd :: tl -> join (carry p hd) tl c;;

(* Problem 6b.  Do a test case or two, to show that the (join p q c) is
  a well-formed priority queue.  More work here will save enormous time
  later. 
*)

let queue1 = Node(2, Leaf, Leaf);;
let queue2 = Node(3, Leaf, Leaf);;
let priq12 = join [queue1] [queue2] Leaf;;
let test_join = priq priq12;;
let queue3 = Node(5, Node(4, Leaf, Leaf), Leaf);;
let priq13 = join [queue1;queue3] [queue2] Leaf;;
let test_join = priq priq13;;
let priq23 = join [queue1;queue3] [queue2] (Node(1, Leaf, Leaf));;

let queue1 = List.fold_left insert emptyQ [3;1;4;1;5;9;2;3;5];;
let queue2 = List.fold_left insert emptyQ [1;2;7;8];;
let queue3 = List.fold_left insert emptyQ [5;6;9;2];;
let test_join1 = priq (join queue1 queue3 tree2);;


(* Deletion of the spine.
   Sedgewick's Figure 9.18 shows that "Taking away the root [of a 
   power-of-2 heap] gives a forest of power-of-2 heaps, all left-heap-ordered,
   with roots from the right spine of the tree."
*)


(*  Problem 7.  The "delete-spine" function, below, deletes the spine
  from a complete balanced binary tree.  Explain what the "cont"
  argument is doing.  Do the explanation by unfolding the
  application of "unzip" to a tree of depth 3.
*)

let rec unzip (t: key tree) (cont: key priqueue -> key priqueue) : key priqueue =
  match t with
    Node(x,t1,t2) -> unzip t2 (fun q -> Node(x,t1,Leaf) :: cont q)
  | Leaf -> cont []

let delete_spine (t: key tree) = unzip t (fun u -> u);;

(* cont is used to reverse the bin2heaps in priqueue *)

(* Problem 8.  Implement a function that deletes (and discards)
   the maximum element of a power-of-2 heap, returning a
   priqueue (that is, a list of power-of-2 heaps).
   Demonstrate this on queue1.
*)

let heap_delete_max (t: key tree) : key priqueue = 
  delete_spine (left t);;

(* Deletion of the max element of a binomial queue is done as follows:
  Suppose the i'th list element has the max element.
  Delete the spine of the i'th element, yielding list l1.
  Let l2 be the original list, but with a Leaf where the i'th element was.
  Now join these two lists.
  Problem 9.  Implement delete_max.  It should return the max element,
   along with the remaining queue.
  It should raise Empty if there were no elements in q.
*)

let rec delmax_help (p : key priqueue) (q : key priqueue) (k : key) : key priqueue = 
   if (root (List.hd q)) = k
   then join (heap_delete_max (List.hd q)) (List.append p (List.tl q)) Leaf
   else delmax_help (List.append p ([List.hd q])) (List.tl q) k;;

let delete_max (q: key priqueue) : key * key priqueue =
   let mx = (find_max q) in (mx, (delmax_help emptyQ q mx));;

(* Problem 9b.  Demonstrate delete_max on queue1.
  Then, demonstrate that repeating delete_max on a priority queue
   gives a sorted list of the elements.
*)

let queue1 = List.fold_left insert emptyQ [3;1;4;1;5;9;2;3;5];;

let rec sort (q: key priqueue) : key list =
    try (let (v,q') = delete_max q in v :: sort q') 
    with Empty -> [];;

let l1 = sort queue1;;