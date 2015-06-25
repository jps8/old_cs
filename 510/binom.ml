(* README
 Joe Sheehan, netid jps8, no help besides binom_with_unzip.
 I figured out the unzip function by myself:  NO
 *)


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
   a tree is a power-of-2-heap. If it is a power-of-2-heap with 2^n nodes, 
    then (pow2heap n t) returns unit.
   Otherwise, (pow2heap n t) raises the exception (IllFormed(n,t)).
*)

exception IllFormed of (int * key tree);;

let comp_left (h: int)(t: key tree) : bool = 
  match t with 
    Leaf -> true
  | Node  (hd, l, r) ->  if h >= hd then true else false
;;

let rec depth (t: key tree) : int = 
  match t with
    Leaf -> 0
  | Node (h, l, r) -> 1 + (depth l)
;;

let rec comp_bal (t:key tree) : bool = 
  match t with
    Leaf -> true
  | Node (h, l, r) ->
      (if (depth l) = (depth r) && 
          (comp_left h l) &&
          (comp_bal l) && (comp_bal r) then true
      else false)
;;

let pow2heap (n: int) (t: key tree) : unit = 
  match t with 
    Leaf -> (if n == 0 then () else raise (IllFormed (n, t)))
  | Node (h, l, r) -> 
      (if r = Leaf && (depth l) = n && comp_bal l then ()
        else raise (IllFormed (n,t)))
;;

(* A priority queue (using the binomial queues data structure)
   is a list of trees.  
   The i'th element of the list is either Leaf or it is a
   power-of-2-heap with exactly 2^i nodes.
*)

type 'a priqueue = 'a tree list;;

let emptyQ : 'a priqueue = [];;

(* Problem 2.  Implement a function     priq: key priqueue -> unit
  that checks whether a priority queue is well formed.
  If it is not well formed, raise the exception Illformed(n,t)
  to complain about the specific list element that is bad; otherwise
  return ().
*)

let rec priqer (q:key priqueue) : unit = 
    match q with 
      [] -> ()
    | hd::tl ->
        (match hd with
            Leaf -> priqer tl
          | Node (_,_,_) -> (pow2heap ((depth hd)-1) hd;
                             priqer tl))
;;

let priq (q: key priqueue) : unit  = 
  priqer q
;;

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
  if (depth t) != (depth u) then raise SmashError
  else match (t, u) with
    (Leaf, _) -> raise SmashError
  | (_, Leaf) -> raise SmashError 
  | (Node (ht, lt, rt), Node (hu, lu, ru)) ->
      (if (ht >= hu) then (
                           let new_tree = Node (hu, lu, lt) in
                            Node (ht, new_tree, Leaf))
      else (
                           let new_tree = Node (ht, lt, lu) in
                            Node (hu, new_tree, Leaf)))

;;     
(* Problem 3a.  Demonstrate a test case.  Do more than one if you
   want to save time later by having debugged this part early.  *)

let tree1 : key tree = 
    let node1 = Node (1, Leaf, Leaf) in
    let node3 = Node (3, Leaf, Leaf) in
    let node2 = Node (2, node1, node3) in
    Node (4, node2, Leaf)
;;
let test_tree1 = pow2heap 2 tree1;;
let tree2 : key tree =   
    let node6 = Node (6, Leaf, Leaf) in
    let node8 = Node (8, Leaf, Leaf) in
    let node7 = Node (7, node6, node8) in
    Node (9, node7, Leaf)
;;
let test_tree2 = pow2heap 2 tree2;;
let tree12 = smash tree1 tree2;;
let test_tree12 = pow2heap 3 tree12;;

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
  match (t, q) with
    (Leaf, _) -> q
  | (Node (_,_,_), []) -> [t]
  | (Node (_,_,_), hd::tl) -> if (depth hd) = (depth t) then 
                              (carry tl (smash hd t))
                              else hd::(carry tl t)
;;

let insert (q: key priqueue) (x: key) : key priqueue = 
  carry q (Node (x, Leaf, Leaf))
;;
(* Problem 4b.  Do a test case.  *)

let queue1 = List.fold_left insert emptyQ [3;1;4;1;5;9;2;3;5];;
let queue2 = List.fold_left insert emptyQ [1;2;7;8;100;-13];;
let queue3 = List.fold_left insert emptyQ [5;6;9;2;0;7];;

let test_queue1 = priq queue1;;
let test_queue2 = priq queue2;;
let test_queue3 = priq queue2;;


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

  let rec maxxer (cur:key) (kq:key priqueue) : key = 
    match kq with
      [] -> cur
    | Leaf::tl -> maxxer cur tl
    | Node (h,l,r)::tl -> (if h > cur then maxxer h tl
                            else maxxer cur tl)
  in

  match q with
    [] -> raise Empty
  | Leaf::tl -> find_max tl
  | Node (h,l,r)::tl  -> maxxer h tl
;;

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
  match p with
    [] -> carry q c
  | hd::tl -> join tl (carry q hd) c
;;

(* Problem 6b.  Do a test case or two, to show that the (join p q c) is
  a well-formed priority queue.  More work here will save enormous time
  later. 
*)

let test_join1 = priq (join queue1 queue3 tree2);;
let test_join1 = priq (join queue2 queue3 tree12);;
let test_join1 = priq (join queue2 queue1 Leaf);;
let test_join1 = priq (join queue1 queue1 tree12);;

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
    Leaf -> cont []
  | Node(x,t1,t2) -> unzip t2 (fun q -> Node(x,t1,Leaf) :: cont q)
;;

let delete_spine (t: key tree) = unzip t (fun u -> u);;

(* EXPLANATION: The cont function allows us to store the list of all the 
    trees found so far as an unevaluated function return value, 
    effectively memoizing the unzipping computation or making it lazy
    which avoids recomputing results.

    Imagine you have a tree that looks like this:
            5
        3       7
      2   4   6   8
    or,
    Node(5, Node (3, Node (2, Leaf, Leaf), Node (4, Leaf, Leaf)
    Node (7, Node (6, Leaf, Leaf), Node (8, Leaf, Leaf))).
    After the first call to unzip, you call it again with the arguments
    t = Node (7, Node (6, Leaf, Leaf), Node (8, Leaf, Leaf)),
    and cont = fun q -> 
    Node (5, Node (3, Node (2, Leaf, Leaf), Node (4, Leaf, Leaf)), Leaf).

    After this second call, you call unzip again with the arguments
    t = Node (8, Leaf, Leaf), and cont = fun q ->
    Node (7, Node (6, Leaf, Leaf), Leaf)::(fun q ->
    Node (5, Node (3, Node (2, Leaf, Leaf), Node (4, Leaf, Leaf)), Leaf))
*)


(* Problem 8.  Implement a function that deletes (and discards)
   the maximum element of a power-of-2 heap, returning a
   priqueue (that is, a list of power-of-2 heaps).

   Demonstrate this on queue1.
*)

let heap_delete_max (t: key tree) : key priqueue = 
  match t with
    Leaf -> emptyQ
  | Node(h,l,r) -> delete_spine l
;;

(* Not sure how to demonstrate this on queue1 so I will demonstrate
   on a tree instead *)
let heap_delete_test1 = priq (heap_delete_max tree12);;

(* Deletion of the max element of a binomial queue is done as follows:
  Suppose the i'th list element has the max element.
  Delete the spine of the i'th element, yielding list l1.
  Let l2 be the original list, but with a Leaf where the i'th element was.
  Now join these two lists.


  Problem 9.  Implement delete_max.  It should return the max element,
   along with the remaining queue.
  It should raise Empty if there were no elements in q.
*)

let delete_max (q: key priqueue) : key * key priqueue = 
  let max = find_max q in

  let rec max_deleter (nq: key priqueue) (n:key) : key priqueue =
    match nq with
      [] -> emptyQ
    | Leaf::tl -> max_deleter tl n
    | Node(h,l,r)::tl ->  if h = n then 
                          join (heap_delete_max (Node(h,l,r))) tl Leaf
                          else carry (max_deleter tl n) (Node(h,l,r))
  in

  (max, max_deleter q max)
;;

(* Problem 9b.  Demonstrate delete_max on queue1.
  Then, demonstrate that repeating delete_max on a priority queue
   gives a sorted list of the elements.
*)

exception DeleteMaxFailure;;

(* allows me to test delete_max *)
let delete_max_tester (q:key priqueue) : int = 
  match delete_max q with 
    (max, q) -> max
;;

(* test on queue1 *)
let delete_max_test1 = 
  if delete_max_tester queue1 != 9 then 
  raise DeleteMaxFailure
;;

let rec sort (q: key priqueue) : key list =
    try (let (v,q') = delete_max q in v :: sort q') 
    with Empty -> [];;

let l1 = sort queue1;;

(* test that repeatedly deleting_max creates a sorted list *)
let rec sort_tester (l:key list) (n:key) =
  match l with
    [] -> ()
  | hd::tl -> if hd > n then raise DeleteMaxFailure
              else sort_tester tl hd
;;

(* test sorted list property on queue1 *)
let sort_test1 = sort_tester l1 999 ;;


