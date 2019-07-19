(* HEADER
  Jacob Adley 
  Verified implementation of Leftist-Min-Heap
  http://typeocaml.com/2015/03/12/heap-leftist-heap/
  *)

(* Arguments ... : simpl never. *)

(* IMPORTS *)
(*From VFA *)Require Import Perm.
(*From QuickChick Require Import QuickChick.*)
Require Import Coq.Logic.FunctionalExtensionality.

(* --- DEFINITIONS --- *)
Variable default : nat.

Axiom le_default:
  forall n : nat, n < default.

Axiom min_default:
  forall n : nat, (min n default) = n.

(* bounds nw ne sw se *)
Inductive heap : Type :=
  | E : heap
    (* left value right rank (length of path to rightmost E) *)
  | T : heap -> nat -> heap -> nat -> heap.

Definition empty_heap := E.

Definition rank (t: heap) :=
  match t with
  | E => 0
  | T _ _ _ rnk => rnk
  end.

Fixpoint size (t: heap) :=
  match t with
  | E => 0
  | T l _ r _ => S ((size l) + (size r))
  end.

(* rank of right child is always <= rank of left child *)
Fixpoint merge (t1: heap) := fix merge_r (t2: heap) :=
  match t1,t2 with
  | E, _ => t2
  | _, E => t1
  | T l1 v1 r1 _, T l2 v2 r2 _ =>
      if (v1 >? v2)
      then
        if ((rank (merge_r r2)) <=? (rank l2))
        then T l2 v2 (merge_r r2) (S (rank (merge_r r2)))
        else T (merge_r r2) v2 l2 (S (rank l2))
      else
        if ((rank (merge r1 t2)) <=? (rank l1))
        then T l1 v1 (merge r1 t2) (S (rank (merge r1 t2)))
        else T (merge r1 t2) v1 l1 (S (rank l1))
  end.

Definition singleton (v: nat) :=
  T E v E 1.

Definition insert (v: nat) (t: heap) :=
  merge (singleton v) t.

Definition heap_min (t: heap) :=
  match t with
  | E => default
  | T _ v _ _ => v
  end.

Definition deletemin (t: heap) :=
  match t with
  | E => E
  | T l _ r _ =>
      merge l r
  end.

(* --- PROPERTIES --- *)
Inductive HeapProp: heap -> Prop :=
  | HP_E : HeapProp E
  (*
  | HP_T: forall l v r rk,
      v <= heap_min l ->
      v <= heap_min r ->
      HeapProp (T l v r rk).
      *)
  | HP_T_EE : forall v rnk,
      HeapProp (T E v E rnk)
  | HP_T_TE : forall v rnk l1 v1 r1 rnk1,
      HeapProp (T l1 v1 r1 rnk1) ->
      v <= v1 ->
      HeapProp (T (T l1 v1 r1 rnk1) v E rnk)
  | HP_T_ET : forall v rnk l2 v2 r2 rnk2,
      HeapProp (T l2 v2 r2 rnk2) ->
      v <= v2 ->
      HeapProp (T E v (T l2 v2 r2 rnk2) rnk)
  | HP_T_TT : forall v rnk l1 v1 r1 rnk1 l2 v2 r2 rnk2,
      HeapProp (T l1 v1 r1 rnk1) ->
      HeapProp (T l2 v2 r2 rnk2) ->
      v <= v1 ->
      v <= v2 ->
      HeapProp (T (T l1 v1 r1 rnk1) v (T l2 v2 r2 rnk2) rnk).

Inductive LeftistProp: heap -> Prop :=
  | LP_E : LeftistProp E
  | LP_T : forall l v r rnk,
      LeftistProp l ->
      LeftistProp r ->
      (rank r) <= (rank l) ->
      LeftistProp (T l v r rnk).

Inductive RankProp: heap -> Prop :=
  | RP_E : RankProp E
  | RP_T : forall l v r rnk,
      RankProp r ->
      (rank (T l v r rnk)) = (S (rank r)) ->
      RankProp (T l v r rnk).

(* --- TESTS --- *)
(* HeapProp *)
Example heap0:
  HeapProp E.
Proof. repeat constructor; auto. Qed.
Example heap1:
  HeapProp (singleton 1).
Proof. repeat constructor; auto. Qed.
Example heap2:
  HeapProp (insert 2 (singleton 1)).
Proof. repeat constructor; auto. Qed.
Example heap3:
  HeapProp (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))).
Proof. repeat constructor; auto. Qed.
Example heap4:
  HeapProp (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))).
Proof. repeat constructor; auto. Qed.
Example heap5:
  HeapProp (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))))).
Proof. repeat constructor; auto. Qed.
Example heap6:
  HeapProp (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))).
Proof. repeat constructor; auto. Qed.
Example heap10:
  HeapProp (singleton 4).
Proof. repeat constructor; auto. Qed.
Example heap11:
  HeapProp (insert 3 (singleton 4)).
Proof. repeat constructor; auto. Qed.
Example heap12:
  HeapProp (insert 0 (insert 3 (singleton 4))).
Proof. repeat constructor; auto. Qed.
Example heap13:
  HeapProp (insert 6 (insert 0 (insert 3 (singleton 4)))).
Proof. repeat constructor; auto. Qed.
Example heap14:
  HeapProp (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))).
Proof. repeat constructor; auto. Qed.
Example heap15:
  HeapProp (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))).
Proof. repeat constructor; auto. Qed.
Example heap16:
  HeapProp (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))))).
Proof. repeat constructor; auto. Qed.
Example heap17:
  HeapProp (merge (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))) (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))))).
Proof. repeat constructor; auto. Qed.

(* LeftistProp *)
Example heap_0:
  LeftistProp E.
Proof. repeat constructor; auto. Qed.
Example heap_1:
  LeftistProp (singleton 1).
Proof. repeat constructor; auto. Qed.
Example heap_2:
  LeftistProp (insert 2 (singleton 1)).
Proof. repeat constructor; auto. Qed.
Example heap_3:
  LeftistProp (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))).
Proof. repeat constructor; auto. Qed.
Example heap_4:
  LeftistProp (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))).
Proof. repeat constructor; auto. Qed.
Example heap_5:
  LeftistProp (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))))).
Proof. repeat constructor; auto. Qed.
Example heap_6:
  LeftistProp (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))).
Proof. repeat constructor; auto. Qed.
Example heap_10:
  LeftistProp (singleton 4).
Proof. repeat constructor; auto. Qed.
Example heap_11:
  LeftistProp (insert 3 (singleton 4)).
Proof. repeat constructor; auto. Qed.
Example heap_12:
  LeftistProp (insert 0 (insert 3 (singleton 4))).
Proof. repeat constructor; auto. Qed.
Example heap_13:
  LeftistProp (insert 6 (insert 0 (insert 3 (singleton 4)))).
Proof. repeat constructor; auto. Qed.
Example heap_14:
  LeftistProp (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))).
Proof. repeat constructor; auto. Qed.
Example heap_15:
  LeftistProp (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))).
Proof. repeat constructor; auto. Qed.
Example heap_16:
  LeftistProp (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))))).
Proof. repeat constructor; auto. Qed.
Example heap_17:
  LeftistProp (merge (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))) (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))))).
Proof. repeat constructor; auto. Qed.

(* RankProp *)
Example heap_0':
  RankProp E.
Proof. repeat constructor; auto. Qed.
Example heap_1':
  RankProp (singleton 1).
Proof. repeat constructor; auto. Qed.
Example heap_2':
  RankProp (insert 2 (singleton 1)).
Proof. repeat constructor; auto. Qed.
Example heap_3':
  RankProp (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))).
Proof. repeat constructor; auto. Qed.
Example heap_4':
  RankProp (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))).
Proof. repeat constructor; auto. Qed.
Example heap_5':
  RankProp (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))))).
Proof. repeat constructor; auto. Qed.
Example heap_6':
  RankProp (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))).
Proof. repeat constructor; auto. Qed.
Example heap_10':
  RankProp (singleton 4).
Proof. repeat constructor; auto. Qed.
Example heap_11':
  RankProp (insert 3 (singleton 4)).
Proof. repeat constructor; auto. Qed.
Example heap_12':
  RankProp (insert 0 (insert 3 (singleton 4))).
Proof. repeat constructor; auto. Qed.
Example heap_13':
  RankProp (insert 6 (insert 0 (insert 3 (singleton 4)))).
Proof. repeat constructor; auto. Qed.
Example heap_14':
  RankProp (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))).
Proof. repeat constructor; auto. Qed.
Example heap_15':
  RankProp (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))).
Proof. repeat constructor; auto. Qed.
Example heap_16':
  RankProp (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))))).
Proof. repeat constructor; auto. Qed.
Example heap_17':
  RankProp (merge (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))) (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))))).
Proof. repeat constructor; auto. Qed.

(* Size *)
Example size_0:
  size E = 0.
Proof. simpl. auto. Qed.
Example size_1:
  size (singleton 1) = 1.
Proof. simpl. auto. Qed.
Example size_2:
  size (insert 2 (singleton 1)) = 2.
Proof. simpl. auto. Qed.
Example size_3:
  size (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))) = 4.
Proof. simpl. auto. Qed.
Example size_4:
  size (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))) = 5.
Proof. simpl. auto. Qed.
Example size_5:
  size (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1))))) = 6.
Proof. simpl. auto. Qed.
Example size_6:
  size (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))) = 7.
Proof. simpl. auto. Qed.
Example size_10:
  size (singleton 4) = 1.
Proof. simpl. auto. Qed.
Example size_11:
  size (insert 3 (singleton 4)) = 2.
Proof. simpl. auto. Qed.
Example size_12:
  size (insert 0 (insert 3 (singleton 4))) = 3.
Proof. simpl. auto. Qed.
Example size_13:
  size (insert 6 (insert 0 (insert 3 (singleton 4)))) = 4.
Proof. simpl. auto. Qed.
Example size_14:
  size (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))) = 5.
Proof. simpl. auto. Qed.
Example size_15:
  size (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))) = 6.
Proof. simpl. auto. Qed.
Example size_16:
  size (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4))))))) = 7.
Proof. simpl. auto. Qed.
Example size_17:
  size (merge (insert 3 (insert 7 (insert 0 (merge (insert 2 (singleton 1)) (insert 2 (singleton 1)))))) (insert 3 (insert 8 (insert 2 (insert 6 (insert 0 (insert 3 (singleton 4)))))))) = 14.
Proof. simpl. auto. Qed.

(* Tactics *)
Ltac crush_heap :=
  repeat match goal with
    | |- HeapProp _ => repeat constructor; auto; omega
    | |- LeftistProp _ => repeat constructor; auto; omega
    | |- RankProp _ => repeat constructor; auto; omega
    | |- context [merge _ _] => unfold merge
    | |- context [if rank _ <=? rank _ then _ else _] => unfold rank
    | |- context [if ?x then _ else _] => bdestruct x
    | |- _ => assumption
  end.
Ltac crush_heap2 :=
  repeat match goal with
    | |- HeapProp _ => repeat constructor; auto; omega
    | |- LeftistProp _ => repeat constructor; auto; omega
    | |- RankProp _ => repeat constructor; auto; omega
    | |- context [merge _ _] => unfold merge
    | |- context [if rank _ <=? rank _ then _ else _] => unfold rank
    | |- context [if ?x then _ else _] => bdestruct x
    | H: HeapProp (T _ _ _ _) |- _ => inv H
    | H: LeftistProp (T _ _ _ _) |- _ => inv H
    | H: RankProp (T _ _ _ _) |- _ => inv H
    | |- _ => assumption
  end.

(* --- THEOREMS --- *)
Lemma le_impl_lt:
  forall n m,
    n < m -> n <= m.
Proof.
  intros. omega.
Qed.

Lemma min_assoc:
  forall n m p,
    min n (min m p) = min (min n m) p.
Proof.
  intros. apply Min.min_assoc.
Qed.

Lemma T_neq_E:
  forall l v r rk, T l v r rk <> E.
Proof.
  intros. intro H. inversion H.
Qed.

Lemma E_neq_T:
  forall l v r rk, E <> T l v r rk.
Proof.
  intros. intro H. inversion H.
Qed.

Lemma merge_neq_E:
  forall l v r rk t, merge (T l v r rk) t <> E.
Proof.
  intros. destruct t; simpl.
  apply T_neq_E.

  repeat match goal with
    | |- (if ?x then _ else _) <> _ => bdestruct x
    | |- T _ _ _ _  <> E => apply T_neq_E
  end.
Qed.

Lemma E_neq_merge:
  forall l v r rk t, E <> merge (T l v r rk) t.
Proof.
  intros. destruct t; simpl.
  apply E_neq_T.

  repeat match goal with
    | |- _ <> (if ?x then _ else _) => bdestruct x
    | |- E <> T _ _ _ _ => apply E_neq_T
  end.
Qed.

Lemma insert_not_E:
  forall v t, insert v t <> E.
Proof.
  intros.
  unfold insert.
  unfold singleton.
  apply merge_neq_E.
Qed.

Lemma E_not_insert:
  forall v t, E <> insert v t.
Proof.
  intros.
  unfold insert.
  unfold singleton.
  apply E_neq_merge.
Qed.

Theorem merge_right_E:
  forall t,
    (merge t E) = t.
Proof.
  intros. destruct t; simpl; auto.
Qed.

Theorem merge_left_E:
  forall t,
    (merge E t) = t.
Proof.
  intros. destruct t; simpl; auto.
Qed.

Lemma rank_zero:
  rank E = 0.
Proof.
  simpl. auto.
Qed.

Theorem rank_sub1_right:
  forall l v r rk,
    RankProp (T l v r rk) ->
    (rank (T l v r rk)) = (S (rank r)).
Proof.
  intros.
  inv H.
  inv H5.
  omega.
Qed.

Theorem empty_Heap:
  HeapProp E.
Proof.
  constructor.
Qed.

Theorem empty_Leftist:
  LeftistProp E.
Proof.
  constructor.
Qed.

Theorem empty_Rank:
  RankProp E.
Proof.
  constructor.
Qed.

Theorem heap_prop_min:
  forall l v r rnk,
    v = heap_min (T l v r rnk).
Proof.
  intros. unfold heap_min. auto.
Qed.

Lemma ins_E:
  forall v,
    (T E v E 1) = insert v E.
Proof.
  intros.
  unfold insert.
  simpl.
  auto.
Qed.

Theorem lt_Heap:
  forall l v r rk w,
    HeapProp (T l v r rk) ->
    w <= v ->
    HeapProp (T l w r rk).
Proof.
  intros. inv H; crush_heap.
  (*intros. crush_heap2.*)
Qed.

Lemma heap_impl_children:
  forall l v r rk,
    HeapProp (T l v r rk) ->
    HeapProp l /\ HeapProp r.
Proof.
  intros. inv H.
  - constructor.
    + constructor.
    + constructor.
  - constructor.
    + auto.
    + constructor.
  - constructor.
    + constructor.
    + auto.
  - constructor.
    + auto.
    + auto.
Qed.

Lemma heap_impl_le:
  forall l v r rk,
    HeapProp (T l v r rk) ->
    v <= heap_min l /\ v <= heap_min r.
Proof.
  intros. inv H; simpl.
  - constructor.
    + apply (le_impl_lt _ _ (le_default _)).
    + apply (le_impl_lt _ _ (le_default _)).
  - constructor.
    + auto.
    + apply (le_impl_lt _ _ (le_default _)).
  - constructor.
    + apply (le_impl_lt _ _ (le_default _)).
    + auto.
  - constructor.
    + auto.
    + auto.
Qed.

Lemma eq_impl_size_eq:
  forall h1 h2,
    h1 = h2 -> size h1 = size h2.
Proof.
  intros. rewrite H. auto.
Qed.

Lemma size_T:
  forall l v r rk,
    size (T l v r rk) = S (size l) + (size r).
Proof.
  intros. simpl. auto.
Qed.

Lemma lr_neq_impl_neq:
  forall l1 v1 r1 rk1 l2 v2 r2 rk2,
    l1 <> l2 \/ r1 <> r2 ->
    (T l1 v1 r1 rk1) <> (T l2 v2 r2 rk2).
Proof.
  intros.
  intro.
  inversion H0.
  inversion H.
  - apply H1 in H2.
    inversion H2.
  - apply H1 in H4.
    inversion H4.
Qed.

Lemma l_neq_impl_neq:
  forall l1 v1 r1 rk1 l2 v2 r2 rk2,
    l1 <> l2 ->
    (T l1 v1 r1 rk1) <> (T l2 v2 r2 rk2).
Proof.
  intros.
  intro.
  inversion H0.
  apply H in H2.
  inversion H2.
Qed.

Lemma r_neq_impl_neq:
  forall l1 v1 r1 rk1 l2 v2 r2 rk2,
    r1 <> r2 ->
    (T l1 v1 r1 rk1) <> (T l2 v2 r2 rk2).
Proof.
  intros.
  intro.
  inversion H0.
  apply H in H4.
  inversion H4.
Qed.

Lemma singleton_neq_ins_T':
  forall v1 rnk1 v2 v3 rnk2,
    T E v1 E rnk1 <> insert v2 (T E v3 E rnk2).
Proof.
  intros.
  unfold insert.
  unfold singleton.
  crush_heap.
  - inv H0.
  - apply lr_neq_impl_neq.
    left.
    apply E_neq_T.
  - apply lr_neq_impl_neq.
    right.
    apply E_neq_T.
  - apply lr_neq_impl_neq.
    left.
    apply E_neq_T.
Qed.

Theorem size_neq_merge_neq:
  forall h1 h2,
    size h1 <> size h2 ->
    h1 <> h2.
Proof.
  intros h1. induction h1; intros h2; induction h2; simpl; intros.
  - auto.
  - apply E_neq_T.
  - apply T_neq_E.
  - intro.
    inversion H0.
    rewrite H2 in H.
    rewrite H4 in H.
    assert (S (size h2_1) + size h2_2 = S (size h2_1) + size h2_2).
    { auto. }
    apply H in H1.
    inversion H1.
Qed.

Theorem merge_E_implies_E:
  forall h1 h2,
    (merge h1 h2) = E ->
    h1 = E /\ h2 = E.
Proof.
  intros h1. induction h1; intros h2; induction h2; intros; split; auto.
  - apply merge_neq_E in H.
    inversion H.
  - apply merge_neq_E in H.
    inversion H.
Qed.

Lemma size_singleton:
  forall v,
  size (singleton v) = 1.
Proof.
  intros. simpl. auto.
Qed.

Lemma size_lrv:
  forall l v r rk,
    size (T l v r rk) = S ((size l) + (size r)).
Proof.
  intros. simpl. auto.
Qed.

Theorem merge_add_size:
  forall h1 h2,
    size (merge h1 h2) = (size h1) + (size h2).
Proof.
  intros h1. induction h1.
  - intros. induction h2; simpl; auto.
  - intros. induction h2.
    + simpl. auto.
    + rewrite (size_lrv h2_1 n1 h2_2 n2).
Admitted.

Theorem ins_add1_size:
  forall h v,
    size (insert v h) = S (size h).
Proof.
  intros. unfold insert. apply merge_add_size.
Qed.

Theorem delete_sub1_size:
  forall h,
    h <> E ->
    size h = S (size (deletemin h)).
Proof.
  intros h. induction h.
  - intros.
    contradiction H.
    auto.
  - intros.
    unfold deletemin.
    rewrite merge_add_size.
    simpl.
    auto.
Qed.

Fixpoint genHeap (n : nat) :=
  match n with
    | 0 => singleton 0
    | S m => merge (singleton m) (genHeap m)
  end.
(* Compute (genHeap 10). *)

Theorem heap_l:
  forall l v r rk,
    HeapProp (T l v r rk) ->
    HeapProp l.
Proof.
  intros. inv H; crush_heap.
  (*intros. crush_heap2.*)
Qed.

Theorem heap_r:
  forall l v r rk,
    HeapProp (T l v r rk) ->
    HeapProp r.
Proof.
  intros. inv H; crush_heap.
  (*intros. crush_heap2.*)
Qed.

Theorem min_ins_is_heap:
  forall l v r rk,
    HeapProp l ->
    HeapProp r ->
    v <= heap_min l ->
    v <= heap_min r ->
    HeapProp (T l v r rk).
Proof.
  intros. inv H; inv H0; crush_heap.
Qed.

Lemma singleton_neq_ins_T:
  forall v1 rnk1 v2 v3 rnk2,
    T E v1 E rnk1 <> insert v2 (T E v3 E rnk2).
Proof.
  intros.
  assert (size (T E v1 E rnk1) <> size (insert v2 (T E v3 E rnk2))).
  { rewrite ins_add1_size.
    simpl.
    intro.
    inv H. }
  apply (size_neq_merge_neq _ _ H).
Qed.

Theorem merge_Heap:
  forall t1 t2,
    HeapProp t1 ->
    HeapProp t2 ->
    HeapProp (merge t1 t2).
Proof.
Admitted.

Theorem merge_Heap': (* BAD *)
  forall l1 v1 r1 rk1 l2 v2 r2 rk2,
    HeapProp (T l1 v1 r1 rk1) ->
    HeapProp (T l2 v2 r2 rk2) ->
    HeapProp (merge (T l1 v1 r1 rk1) (T l2 v2 r2 rk2)).
Proof.
  intros. inv H. inv H0.
  * unfold merge.
    bdestruct (v2 <? v1).
    unfold rank.
    (* bdestruct (0 <=? rank E). *)
    - bdestruct (rk1 <=? 0).
      + constructor.
        -- constructor.
        -- omega.
      + constructor.
        -- constructor.
        -- omega.
    - unfold rank.
      bdestruct (rk2 <=? 0).
      + constructor.
        -- constructor.
        -- omega.
      + constructor.
        -- constructor.
        -- omega.
  * unfold merge. 
    bdestruct (v2 <? v1).
    - unfold rank.
      bdestruct (rk1 <=? rnk1).
      + constructor.
        -- auto.
        -- constructor.
        -- omega.
        -- omega.
      + constructor.
        -- constructor.
        -- auto.
        -- omega.
        -- omega.
    - unfold rank.
      bdestruct (rk2 <=? 0).
      + constructor.
        -- constructor.
           ++ auto.
           ++ auto.
        -- auto.
      + repeat constructor; auto.
  * 
Abort.

Theorem merge_Heap'':
  forall t1 t2,
    HeapProp t1 ->
    HeapProp t2 ->
    HeapProp (merge t1 t2).
Proof.
  intros t1 t2 H1 H2. revert H1. revert t1. induction H2; intros.
  - induction t1; crush_heap.
  - (*inv H1;
    repeat match goal with
      | |- HeapProp _ => repeat constructor; auto; omega
      | |- context [if ?x then _ else _] => bdestruct x
      (*| |- context [merge ?h1 ?h2] => induction h1; induction h2*)
      | |- context [merge _ _] => unfold merge
      | |- context [if rank _ <=? rank _ then _ else _] => unfold rank
      | H: HeapProp (T _ _ _ _) |- _ => inv H 
      | |- _ => assumption
    end.*)
Abort.

Theorem merge_Heap''':
  forall t1 t2,
    HeapProp t1 ->
    HeapProp t2 ->
    HeapProp (merge t1 t2).
Proof.
  intros t1. induction t1; intros t2; induction t2; intros H1; induction H1; intros H2; induction H2.
  - crush_heap.
  - crush_heap.
  - crush_heap.
Abort.

Theorem merge_Leftist:
  forall t1 t2,
    LeftistProp t1 ->
    LeftistProp t2 ->
    LeftistProp (merge t1 t2).
Proof.
  intros. induction H; induction H0.
  - simpl. constructor.
  - simpl. constructor; auto.
  - simpl. constructor; auto.
  - admit.
Admitted.

Theorem merge_Rank:
  forall t1 t2,
    RankProp t1 ->
    RankProp t2 ->
    RankProp (merge t1 t2).
Proof.
  intros. induction H; induction H0.
  - simpl. constructor.
  - simpl. constructor; auto.
  - simpl. constructor; auto.
  - admit.
Admitted.

Corollary insert_Heap:
  forall h v,
    HeapProp h ->
    HeapProp (insert v h).
Proof.
  intros.
  unfold insert.
  apply merge_Heap.
  constructor.
  auto.
Qed.

Corollary insert_Leftist:
  forall h v,
    LeftistProp h ->
    LeftistProp (insert v h).
Proof.
  intros.
  unfold insert.
  apply merge_Leftist.
  repeat constructor.
  auto.
Qed.

Corollary insert_Rank:
  forall h v,
    RankProp h ->
    RankProp (insert v h).
Proof.
  intros.
  unfold insert.
  apply merge_Rank.
  repeat constructor.
  auto.
Qed.

Fixpoint list_min ls :=
  match ls with
  | [] => default
  | c :: [] => c
  | c :: d => 
      if c <? list_min d
      then c
      else list_min d
  end.

(* --- list_min TESTS --- *)
Example list_min0:
  default = list_min [ ].
Proof.
  simpl. auto.
Qed.

Example list_min1:
  1 = list_min [ 1 ].
Proof.
  simpl. auto.
Qed.

Example list_min10:
  1 = list_min [ 5 ; 6 ; 2 ; 9 ; 3 ; 7 ; 1 ; 8 ; 10 ; 4 ].
Proof.
  simpl. auto.
Qed.

Lemma list_min_null:
  list_min [] = default.
Proof.
  auto.
Qed.

Lemma min_app':
  forall l1 l2, list_min (l1 ++ l2) = min (list_min l1) (list_min l2).
Proof.
  intros l1; induction l1; intros l2; induction l2.
  - simpl. rewrite min_default. auto.
  - simpl in IHl2.
    rewrite list_min_null.
Abort.

Lemma min_cons:
  forall v l, list_min (v :: l) = min v (list_min l).
Proof.
  intros. induction l.
  - unfold list_min.
    rewrite min_default.
    auto.
  - 
Admitted.

Lemma min_app:
  forall l1 l2, list_min (l1 ++ l2) = min (list_min l1) (list_min l2).
Proof.
  intros. induction l1.
  - simpl.
    rewrite Nat.min_comm.
    rewrite min_default.
    auto.
  - rewrite min_cons.
    rewrite <- app_comm_cons.
    rewrite min_cons.
    rewrite IHl1.
    rewrite Min.min_assoc.
    rewrite <- min_assoc.
    auto.
Qed.

(* --- Abstraction Relationships --- *)
Module AbsRel0.
  Inductive Abs: heap -> list nat -> Prop :=
    | Abs_E: Abs E []
    | Abs_T: forall h1 h2 l1 l2 rk v,
        Abs h1 l1 ->
        Abs h2 l2 ->
        Abs (T h1 v h2 rk) (v :: (l1 ++ l2)).

  Theorem empty_relate:
    Abs E [].
  Proof.
    constructor.
  Qed.

  Theorem min_relate:
    forall h l, Abs h l -> HeapProp h -> heap_min h = list_min l.
  Proof.
    intros h l H. induction H; intros.
    - simpl. auto.
    - assert (HeapProp h1).
      { apply heap_impl_children in H1.
        apply H1. }
      assert (HeapProp h2).
      { apply heap_impl_children in H1.
        apply H1. }
      apply IHAbs1 in H2.
      apply IHAbs2 in H3.
      rewrite min_cons.
      assert (v <= heap_min h1).
      { apply (heap_impl_le _ _ _ _ H1). }
      assert (v <= heap_min h2).
      { apply (heap_impl_le _ _ _ _ H1). }
      assert (list_min (l1 ++ l2) = min (list_min l1) (list_min l2)).
      { apply min_app. }
      rewrite H6.
      rewrite Nat.min_assoc.
      rewrite H2 in H4.
      rewrite H3 in H5.
      rewrite min_l.
      rewrite min_l; auto.
      rewrite min_l; auto.
  Qed.

  Theorem size_relate:
    forall h l,
      Abs h l ->
      size h = length l.
  Proof.
    intros. induction H.
    - simpl. auto.
    - simpl. 
      rewrite IHAbs1.
      rewrite IHAbs2.
      rewrite app_length.
      auto.
  Qed.

  Lemma relate_singleton:
    forall v,
      Abs (singleton v) [v].
  Proof.
    intros.
    unfold singleton. 
    Check Abs_T.
    apply (Abs_T E E [] [] 1 v empty_relate empty_relate).
  Qed.

  Lemma abs_E_l:
    forall l,
      Abs E l ->
      l = [].
  Proof.
    intros l. induction l; intros.
    - auto.
    - inversion H.
  Qed.

  Lemma abs_h_e:
    forall h,
      Abs h [] ->
      h = E.
  Proof.
    intros h. induction h; intros.
    - auto.
    - inversion H.
  Qed.

  Theorem insert_relate:
    forall h l v,
      Abs h l ->
      Abs (insert v h) (v :: l).
  Proof.
  Abort.

  Theorem merge_relate:
    forall h1 h2 l1 l2,
      Abs h1 l1 ->
      Abs h2 l2 ->
      Abs (merge h1 h2) (l1 ++ l2).
  Proof.
  Abort.
End AbsRel0.

Module AbsRel1.
  Inductive Abs: heap -> list nat -> Prop :=
    | Abs_E: Abs E []
    | Abs_T: forall h1 h2 l1 l2 rk v,
        Abs h1 l1 ->
        Abs h2 l2 ->
        Abs (T h1 v h2 rk) (v :: (l1 ++ l2)).

  Lemma empty_relate:
    Abs E [].
  Proof.
    constructor.
  Qed.

  Theorem min_relate:
    forall h l, Abs h l -> HeapProp h -> heap_min h = list_min l.
  Proof.
    intros h l H. induction H; intros.
    - simpl. auto.
    - assert (HeapProp h1).
      { apply heap_impl_children in H1.
        apply H1. }
      assert (HeapProp h2).
      { apply heap_impl_children in H1.
        apply H1. }
      apply IHAbs1 in H2.
      apply IHAbs2 in H3.
      rewrite min_cons.
      assert (v <= heap_min h1).
      { apply (heap_impl_le _ _ _ _ H1). }
      assert (v <= heap_min h2).
      { apply (heap_impl_le _ _ _ _ H1). }
      assert (list_min (l1 ++ l2) = min (list_min l1) (list_min l2)).
      { apply min_app. }
      rewrite H6.
      rewrite Nat.min_assoc.
      rewrite H2 in H4.
      rewrite H3 in H5.
      rewrite min_l.
      rewrite min_l; auto.
      rewrite min_l; auto.
  Qed.

  Theorem size_relate:
    forall h l,
      Abs h l ->
      size h = length l.
  Proof.
    intros. induction H.
    - simpl. auto.
    - simpl. 
      rewrite IHAbs1.
      rewrite IHAbs2.
      rewrite app_length.
      auto.
  Qed.

  Lemma relate_singleton:
    forall v,
      Abs (singleton v) [v].
  Proof.
    intros.
    unfold singleton. 
    Check Abs_T.
    apply (Abs_T E E [] [] 1 v empty_relate empty_relate).
  Qed.

  Lemma abs_E_l:
    forall l,
      Abs E l ->
      l = [].
  Proof.
    intros l. induction l; intros.
    - auto.
    - inversion H.
  Qed.

  Lemma abs_h_e:
    forall h,
      Abs h [] ->
      h = E.
  Proof.
    intros h. induction h; intros.
    - auto.
    - inversion H.
  Qed.

  (*these two theorems might be impossible with current abs relation ...*)
  Theorem insert_relate:
    forall h l v,
      Abs h l ->
      Abs (insert v h) (v :: l).
  Proof.
  Abort.

  Theorem merge_relate:
    forall h1 h2 l1 l2,
      Abs h1 l1 ->
      Abs h2 l2 ->
      Abs (merge h1 h2) (l1 ++ l2).
  Proof.
  Abort.
End AbsRel1.

Module AbsRel2.
  Fixpoint heap_In (n : nat) (h : heap) :=
    match h with
    | E => False
    | T l v r _ =>
        if n =? v
        then True
        else (heap_In n l \/ heap_In n r)
    end.

  Inductive Abs: heap -> list nat -> Prop :=
    | Abs_E: Abs E []
    | Abs_T: forall h1 h2 l rk v,
        (forall (n : nat), ((heap_In n h1 \/ heap_In n h2) <-> In n l)) ->
        Abs (T h1 v h2 rk) (v :: l).

  Lemma empty_relate:
    Abs E [].
  Proof.
    constructor.
  Qed.

  Lemma singleton_relate:
    forall v rk,
      Abs (T E v E rk) [v].
  Proof.
    intros. constructor. intros.
    split; simpl; intro; inv H; auto.
  Qed.

  Lemma abs_h_e:
    forall h,
      Abs h [] ->
      h = E.
  Proof.
    intros h. induction h; intros; auto; inversion H.
  Qed.
  
  Theorem min_relate:
    forall h l, Abs h l -> HeapProp h -> heap_min h = list_min l.
  Proof.
    intros. inv H.
    - simpl. auto.
    - admit.
  Admitted.

  Theorem insert_relate:
    forall h l v,
      Abs h l ->
      Abs (insert v h) (v :: l).
  Proof.
  Abort.

(* Arguments ... : simpl never. *)

  Lemma neq_impl_false:
    forall n : nat,
      n <> n -> False.
  Proof.
    intros. induction n; auto.
  Qed.

  Lemma in_lr_impl_in:
    forall l v r rk,
      heap_In v l \/ heap_In v r ->
      heap_In v (T l v r rk).
  Proof.
    intros.
    inv H.
    - simpl.
      bdestruct (v =? v).
      + auto.
      + apply neq_impl_false in H.
        inversion H.
    - simpl.
      bdestruct (v =? v).
      + auto.
      + apply neq_impl_false in H.
        inversion H.
  Qed.

  Theorem merge_relate:
    forall h1 h2 l1 l2,
      Abs h1 l1 ->
      Abs h2 l2 ->
      Abs (merge h1 h2) (l1 ++ l2).
  Proof.
    intros h1 h2 l1 l2 H. induction H; intros.
    - rewrite merge_left_E. simpl. auto.
    - induction H0.
      + simpl.
        rewrite app_nil_r.
        constructor; auto.
      + 
  Abort.
End AbsRel2.
