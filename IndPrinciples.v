(** * IndPrinciples: Induction Principles *)

(** With the Curry-Howard correspondence and its realization in Rocq in
    mind, we can now take a deeper look at induction principles. *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality".
From LF Require Export ProofObjects.

(* ################################################################# *)
(** * Proof by Recursion *)

(** In the previous chapter we saw most of our favorite tactics
    explained as simple programs:

    - destruct is just case analysis (match)
    - apply is function application
    - rewrite is an application of eq_eqL
    - split, left, right, and reflexivity are just applying constructors

    But what about induction?

*)

(** Let's start by writing out a suitable inductive predicate.
    A nice option is the Rocq standard library's definition of even and odd. *)

Inductive even : nat -> Prop :=
| eO : even 0
| eS : forall n, odd n -> even (S n)

with odd : nat -> Prop :=
| oS : forall n, even n -> odd (S n).

(** We just wrote a "mutually inductive" definition.  In short, it
    says that [O] is [Even], the successor of an [Odd] number is
    [Even] and then successor of an [Even] number is [Odd]. *)

(** Here's the lemma we'd like to prove. *)

Lemma even_or_odd : forall (n : nat), even n \/ odd n.
Abort.

(** The proof of even_or_odd is actually quite easy to program! *)

Fixpoint even_or_odd (n : nat) : even n \/ odd n
  (* WORKED IN CLASS *) :=
  match n with
  | 0 => or_introl eO
  | S n' => match even_or_odd n' with
           | or_introl e => or_intror (oS n' e)
           | or_intror o => or_introl (eS n' o)
           end
  end.

(** Unfortunately, writing entire proofs in the programming language
    can be quite hard. Fortunately, there is a simple program that
    makes these proofs easy. *)

Check nat_ind.

(** nat_ind takes four arguments:

    1) A proposition P over natural numbers
    2) A proof of P
    3) A proof that P m -> P (S m).
    4) An arbitrary n

    and it constructs a recursive proof that P n.

    (Equivalently, it takes in three arguments and constructs
    a proof that [forall n, P n].)

    Let's try to prove nat_ind ourselves.

 *)

Fixpoint nat_ind (P : nat -> Prop)
                 (p0 : P 0)
                 (pS : forall m, P m -> P (S m))
                 (n : nat)
                 : P n
  (* WORKED IN CLASS *) :=
  match n with
  | 0    => p0
  | S n' => pS n' (nat_ind P p0 pS n')
  end.


(** We can now use nat_ind to prove even_or_odd in the proof environment *)

Lemma even_or_odd' (n : nat) : even n \/ odd n.
Proof.
  apply nat_ind with (n := n).
  - apply or_introl.
    apply eO.
  - intros n' IHn.
    destruct IHn as [He | Ho].
    + apply or_intror. apply oS. apply He.
    + apply or_introl. apply eS. apply Ho.
Defined.

(* ################################################################# *)
(** * Induction in Depth *)

(** Every time we declare a new [Inductive] datatype, Rocq
    automatically generates an _induction principle_ for this type.
    This induction principle is a theorem like any other: If [t] is
    defined inductively, the corresponding induction principle is
    called [t_ind].  Here is the one for lists: *)

Check list_ind : forall (X : Type) (P : list X -> Prop),
                 P [ ] ->
                 (forall (x : X) (l : list X), P l -> P (x :: l)) ->
                 forall l : list X, P l.

(** As before, we can _prove_ this: *)

Fixpoint list_ind' (X : Type) (P : list X -> Prop)
                   (pnil : P [ ])
                   (pind : forall (x : X) (l : list X), P l -> P (x :: l))
                   (l : list X) : P l :=
  match l with
  | [] => pnil
  | x :: l' => pind x l' (list_ind' X P pnil pind l')
  end.

(** The [induction] tactic is a straightforward wrapper that, at its
    core, simply performs [apply t_ind].  To see this more clearly,
    let's experiment with directly using [apply list_ind], instead of
    the [induction] tactic, to carry out some proofs.  Here, for
    example, is an alternate proof of a theorem that we saw in the
    [Induction] chapter. *)

Theorem app_0_r' : forall {X : Type} (l : list X),
  l ++ [] = l.
Proof.
  intros X.
  apply list_ind.
  - (* l = [] *) reflexivity.
  - (* l = x :: l' *) simpl. intros x l' IH. rewrite -> IH.
    reflexivity.  Qed.

(** This proof is basically the same as the earlier one, but a
    few minor differences are worth noting.

    First, in the induction step of the proof (the ["x :: l"] case), we
    have to do a little bookkeeping manually (the [intros]) that
    [induction] does automatically.

    Second, we do not introduce [l] into the context before applying
    [list_ind] -- the conclusion of [list_ind] is a quantified
    formula, and [apply] needs this conclusion to exactly match the
    shape of the goal state, including the quantifier. (However, we
    can specify [l] using [with].) By contrast, the [induction] tactic
    works either with a variable in the context or a quantified
    variable in the goal.

    Third, we had to manually supply the name of the induction
    principle with [apply], but [induction] figures that out itself.

    These conveniences make [induction] nicer to use in practice than
    applying induction principles like [list_ind] directly.  But it is
    important to realize that, modulo these bits of bookkeeping,
    applying [list_ind] is what we are really doing. *)

(** **** Exercise: 2 stars, standard (len_app')

    Complete this proof without using the [induction] tactic. *)

Theorem len_app' : forall {X : Type} (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2.
  induction l1 as [| h1 t1 IH1].
  - (* Base case: l1 is nil *)
    reflexivity.
  - (* Inductive step: l1 is h1 :: t1 *)
    simpl.
    rewrite -> IH1.
    reflexivity.
Qed.
(** [] *)

(** Rocq generates induction principles for every datatype
    defined with [Inductive], including those that aren't recursive.
    Although of course we don't need the proof technique of induction
    to prove properties of non-recursive datatypes, the idea of an
    induction principle still makes sense for them: it gives a way to
    prove that a property holds for all values of the type. *)

(** These generated principles follow a similar pattern. If we
    define a type [t] with constructors [c1] ... [cn], Rocq generates a
    theorem with this shape:

    t_ind : forall P : t -> Prop,
              ... case for c1 ... ->
              ... case for c2 ... -> ...
              ... case for cn ... ->
              forall n : t, P n

    The specific shape of each case depends on the arguments to the
    corresponding constructor. *)

(** Before trying to write down a general rule, let's look at
    some more examples. First, an example where the constructors take
    no arguments: *)

Inductive time : Type :=
  | day
  | night.

Check time_ind :
  forall P : time -> Prop,
    P day ->
    P night ->
    forall t : time, P t.

(** **** Exercise: 1 star, standard, optional (rgb)

    Write out the induction principle that Rocq will generate for the
    following datatype.  Write down your answer on paper or type it
    into a comment, and then compare it with what Rocq prints. *)

Inductive rgb : Type :=
  | red
  | green
  | blue.
Check rgb_ind.
(** [] *)

(** In general, the automatically generated induction principle for
    inductive type [t] is formed as follows:

    - Each constructor [c] generates one case of the principle.
    - If [c] takes no arguments, that case is:

      "P holds of c"

    - If [c] takes arguments [x1:a1] ... [xn:an], that case is:

      "For all x1:a1 ... xn:an,
          if [P] holds of each of the arguments of type [t],
          then [P] holds of [c x1 ... xn]"

      But that oversimplifies a little.  An assumption about [P]
      holding of an argument [x] of type [t] actually occurs
      immediately after the quantification of [x].
*)

(** For example, suppose we had written the definition of [natlist] a little
    differently: *)

Inductive natlist' : Type :=
  | nnil'
  | nsnoc (l : natlist') (n : nat).

(** Now the induction principle case for [nsnoc] is a bit different
    than the earlier case for [ncons]: *)

Check natlist'_ind :
  forall P : natlist' -> Prop,
    P nnil' ->
    (forall l : natlist', P l -> forall n : nat, P (nsnoc l n)) ->
    forall n : natlist', P n.

(** **** Exercise: 1 star, standard (booltree_ind)

    In the comment below, write out the induction principle that Rocq
    will generate for the following datatype. *)

Inductive booltree : Type :=
  | bt_empty
  | bt_leaf (b : bool)
  | bt_branch (b : bool) (t1 t2 : booltree).

(* Booltree ind 
   ... *)

(* Do not modify the following line: *)
Definition manual_grade_for_booltree_ind : option (nat*string) := None.
(** [] *)

(** **** Exercise: 1 star, standard (toy_ind)

    Here is an induction principle for a toy type:

  forall P : Toy -> Prop,
    (forall b : bool, P (con1 b)) ->
    (forall (n : nat) (t : Toy), P t -> P (con2 n t)) ->
    forall t : Toy, P t

    Give an [Inductive] definition of [Toy], such that the induction
    principle Rocq generates is that given above: *)

Inductive Toy : Type :=
  | con1 (b : bool)
  | con2 (n : nat) (t : Toy).

(* Do not modify the following line: *)
Definition manual_grade_for_toy_ind : option (nat*string) := None.
(** [] *)

(* ################################################################# *)
(** * Induction Principles in [Prop] *)

(** Earlier, we looked in detail at the induction principles that Rocq
    generates for inductively defined _sets_.  The induction
    principles for inductively defined _propositions_ like [even] are a
    tiny bit more complicated.  As with all induction principles, we
    want to use the induction principle on [even] to prove things by
    inductively considering the possible shapes that something in [even]
    can have.  Intuitively speaking, however, what we want to prove
    are not statements about _evidence_ but statements about
    _numbers_: accordingly, we want an induction principle that lets
    us prove properties of numbers by induction on evidence.
    For example:
*)

(** From what we've said so far, you might expect the
    inductive definition of [ev]...

      Inductive ev : nat -> Prop :=
      | ev_0 : even 0
      | ev_SS : forall n : nat, even n -> even (S (S n)).

    ...to give rise to an induction principle that looks like this...

    ev_ind_max : forall P : (forall n : nat, even n -> Prop),
         P O ev_0 ->
         (forall (m : nat) (E : ev m),
            P m E ->
            P (S (S m)) (ev_SS m E)) ->
         forall (n : nat) (E : ev n),
         P n E
*)

(**   ... because:

     - Since [ev] is indexed by a number [n] (every [ev] object [E] is
       a piece of evidence that some particular number [n] is even),
       the proposition [P] is parameterized by both [n] and [E] --
       that is, the induction principle can be used to prove
       assertions involving both an even number and the evidence that
       it is even.

     - Since there are two ways of giving evidence of evenness ([even]
       has two constructors), applying the induction principle
       generates two subgoals:

         - We must prove that [P] holds for [O] and [ev_0].

         - We must prove that, whenever [m] is an even number and [E]
           is an evidence of its evenness, if [P] holds of [m] and
           [E], then it also holds of [S (S m)] and [ev_SS m E].

     - If these subgoals can be proved, then the induction principle
       tells us that [P] is true for _all_ even numbers [n] and
       evidence [E] of their evenness.

    This is more flexibility than we normally need or want: it is
    giving us a way to prove logical assertions where the assertion
    involves properties of some piece of _evidence_ of evenness, while
    all we really care about is proving properties of _numbers_ that
    are even -- we are interested in assertions about numbers, not
    about evidence.  It would therefore be more convenient to have an
    induction principle for proving propositions [P] that are
    parameterized just by [n] and whose conclusion establishes [P] for
    all even numbers [n]:

       forall P : nat -> Prop,
         ... ->
       forall n : nat,
         even n -> P n

    For this reason, Rocq actually generates the following simplified
    induction principle for [ev]: *)

Print ev.

(* ===>

  Inductive ev : nat -> Prop :=
  | ev_0 : ev 0
  | ev_SS : forall n : nat, ev n -> ev (S (S n)))

*)

Check ev_ind :
  forall P : nat -> Prop,
    P 0 ->
    (forall n : nat, ev n -> P n -> P (S (S n))) ->
    forall n : nat, ev n -> P n.

(** In English, [ev_ind] says: Suppose [P] is a property of natural
    numbers.  To show that [P n] holds whenever [n] is even, it suffices
    to show:

      - [P] holds for [0],

      - for any [n], if [n] is even and [P] holds for [n], then [P]
        holds for [S (S n)]. *)

(** As expected, we can apply [ev_ind] directly instead of using
    [induction].  For example, we can use it to show that [ev'] (the
    slightly awkward alternate definition of evenness that we saw in
    an exercise in the [IndProp] chapter) is equivalent to the
    cleaner inductive definition [ev]: *)

Inductive ev' : nat -> Prop :=
  | ev'_0 : ev' 0
  | ev'_2 : ev' 2
  | ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

Theorem ev_ev' : forall n, ev n -> ev' n.
Proof.
  apply ev_ind.
  - (* ev_0 *)
    apply ev'_0.
  - (* ev_SS *)
    intros m Hm IH.
    apply (ev'_sum 2 m).
    + apply ev'_2.
    + apply IH.
Qed.

(* ################################################################# *)
(** * Strengthening Induction Principles *)

(** Sometimes the default kind of induction that Rocq gives you
    isn't sufficient for a given task. Let's try to prove a
    simple theorem about our definition of [even] from the
    beginning of this chapter. *)

(* Try #1 *)

Lemma even_divides_two_try1 : forall n, even n -> exists m, n = m * 2.
Proof.
  (* WORKED IN CLASS *)
  induction n; intros.
  - exists 0; reflexivity.
  -
Abort.

(** Maybe we can do induction on the [even n] predicate? *)

Lemma even_divides_two_try2 : forall n, even n -> exists m, n = m * 2.
Proof.
  intros n e.
  induction e.
  - exists 0; reflexivity.
  - inversion H; subst.
Abort.

(** We're going to need a better induction principle. *)

Fixpoint even_ind'
         (P : nat -> Prop)
         (p0 : P 0)
         (pSS : forall m, even m -> P m -> P (S (S m)))
         (n : nat)
         (e : even n)
         {struct e}
  : P n.
  refine (match e with
          | eO => p0
          | eS n' po => match po with
                       | oS n'' e' => _
                       end
          end).
  apply pSS.
  - apply e'.
  - apply even_ind'.
    + apply p0.
    + apply pSS.
    + apply e'.
Defined.

Lemma even_divides_two : forall n, even n -> exists m, n = m * 2.
Proof.
(* WORKED IN CLASS *)
  intros.
  induction H as [|n' E] using even_ind'.
  -  exists 0. reflexivity.
  - destruct IHE as [m' IHE].
    exists (S m').
    rewrite IHE.
    simpl.
    reflexivity.
Qed.

(** **** Exercise: 3 stars, standard (odd_decomposition)

    Write a corresponding induction principle for odd and
    use it to prove the corresponding lemma about odd numbers. *)

(* Do NOT use the preceding lemma in your proof. *)

(* FILL IN HERE *)

Fixpoint odd_ind'
         (P : nat -> Prop)
         (p1 : P 1)
         (pSS : forall m, odd m -> P m -> P (S (S m)))
         (n : nat)
         (o : odd n)
         {struct o}
  : P n.
Proof.
  refine (
    match o with
    | oS n' e =>
        match e with
        | eO => _
        | eS n'' o' => _
        end
    end).
  - (* n = 1 *)
    exact p1.
  - (* n = S (S n'') *)
    apply pSS.
    + apply o'.
    + apply odd_ind'.
      * exact p1.
      * exact pSS.
      * exact o'.
Defined.

Lemma odd_decomposition : forall n, odd n -> exists m, n = m * 2 + 1.
Proof.
  intros n H.
  induction H using odd_ind'.
  - (* 1 *)
    exists 0. reflexivity.
  - (* S (S m) *)
    destruct IHodd as [m' IH].
    exists (S m').
    rewrite IH.
    simpl.
    reflexivity.
Qed.
(** [] *)

(** Let's look at a more interesting example: an arbitrarily branching tree: *)

Inductive tree :=
| leaf : nat -> tree
| node : list tree -> tree.

Check tree_ind : forall P : tree -> Prop,
                (forall n : nat, P (leaf n)) ->
                (forall l : list tree, P (node l)) ->
                 forall t : tree, P t.

(** Let's see if we can use this to prove the correctness of a tree
    mapping function: *)

Fixpoint map_tree (f : nat -> nat) (t : tree) {struct t} : tree :=
  match t with
  | leaf n => leaf (f n)
  | node l => node (map (map_tree f) l)
  end.

Inductive In_tree : nat -> tree -> Prop :=
| In_leaf : forall n, In_tree n (leaf n)
| In_node : forall n t l, In_tree n t -> In t l -> In_tree n (node l).

Theorem map_correct :
  forall t m f, In_tree m t -> In_tree (f m) (map_tree f t).
Proof.
  intros t.
  induction t.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    constructor.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    (* Now what? *)
Abort.

Fixpoint tree_ind'
         (P : tree -> Prop)
         (Hl : forall n, P (leaf n))
         (Hn : forall l, (forall x, In x l -> P x) -> P (node l))
         (t : tree)
         {struct t} : P t.
  refine (match t with
          | leaf n => Hl n
          | node l => Hn l _
          end).
  induction l.
  - intros t' H. inversion H.
  - intros t' H.
    destruct H.
    + rewrite <- H.
      apply tree_ind'.
      apply Hl.
      apply Hn.
    + apply IHl.
      apply H.
Defined.

Theorem map_correct :
  forall t m f, In_tree m t -> In_tree (f m) (map_tree f t).
Proof.
  intros t.
  induction t using tree_ind'.
  - intros m f HIn. simpl.
    inversion HIn; subst.
    apply In_leaf.
  - intros m f HIn. simpl.
    inversion HIn. subst.
    apply In_node with (map_tree f t).
    + apply H.
      apply H3.
      apply H1.
    + apply In_map.
      apply H3.
Qed.

(* A final, convenient example of an alternative induction
   hypothesis: Strong Induction! *)

From Stdlib Require Import Psatz.

Lemma nat_strong_induction' : forall (P : nat -> Prop),
    P 0 ->
    (forall n , (forall m, m < n -> P m) -> P n) ->
    forall n m, m <= n -> P m.
Proof.
  intros P p0 SI n.
  induction n.
  - intros. inversion H. assumption.
  - intros.
    apply SI.
    intros.
    apply IHn.
    lia.
Qed.

Lemma nat_strong_induction : forall (P : nat -> Prop),
    (forall n , (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros P H n.
  apply nat_strong_induction' with (n:=n).
  - apply H. intros m F. inversion F.
  - intros m H'.
    apply H.
    apply H'.
  - apply le_n.
Qed.


(* 2026-02-10 16:41 *)
