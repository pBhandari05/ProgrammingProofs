(** * ProofObjects: The Curry-Howard Correspondence *)

Set Warnings "-notation-overridden,-parsing,-deprecated-hint-without-locality, -local-declaration".
From LF Require Export IndProp.

(** "Algorithms are the computational content of proofs."
    (Robert Harper) *)

(** Let's start off with the most basic philosophical question:
    What is True?  *)

Print True.
(* ==>
  Inductive True : Prop :=  I : True
*)

(** Straightforward enough.
    What is False? *)
Print False.
(* ==>
  Inductive False : Prop := .
*)

(** We're not missing anything.
    [False] is simply an inductive type with no constructors. *)

(** Like booleans and natural numbers, [True] and [False] have no special
    status. Let's define our own versions. *)

Inductive True' : Prop := yes.
Inductive False' : Prop := .

(** We can think of Rocq Propositions as simply Types where we only care
    _whether_ there is a term of of that type, not what that term is.

    Hence, we can equally well define as True as follows: *)

Inductive True'' :=
| of_course
| naturally.

(** Traditionally, if we want to show that [True''] is "true", we state it as a
    lemma: *)

Lemma True''_is_True : True''.
Proof. apply naturally. Qed.

(** But we could also 'prove' it directly by exhibiting a term of type
    True'' *)

Definition True''_is_True2 : True'' := naturally.

(** This is actually what [apply naturally] produces! *)

Print True''_is_True.
Print True''_is_True2.

(** We will return to the Rocq proof engine and how it works internally
    at the end of this chapter. *)

(* ################################################################# *)
(** * Arrows, Functions and Implication *)

Module functions.

(** So far, we've portrayed Rocq's arrow notation [->] as
    having two distinct meanings: *)

Parameter f : nat -> bool.

(** declares f as a function from [nat] to [bool] while *)

Axiom P : False -> True.

(** states the axiom P that [False] implies [True]. *)

(** In fact, both f and P say "for every A, I can construct a
    B".  Since we only care whether Props have corresponding terms, we
    might summarize this as "if there is an A then there is a B" or "A
    implies B". But the proof demands constructing an element of Prop
    B, hence we call Rocq a "constructive" logic. *)

(** Here are the direct proofs of two basic theorems about True and
    False *)

Definition then_True : forall A, A -> True := fun _ _ => I.

Definition if_False : forall A, False -> A :=
  fun _ F =>
    match F with
    end.

(** That last one may seem funny, but we have indeed constructed an A
    for every element of F - vacuously! This corresponds exactly to our
    proof of ex_falso_quodlibet in Logic.v *)

Lemma ex_falso_quodlibet : forall A, False -> A.
Proof. intros A F. destruct F. Qed.

Print ex_falso_quodlibet.

(** You will notice that Rocq prints [return A] as part of the
    proof term. That tells Rocq what the return type is of the match
    statement. Rocq was able to infer this in our proof of if_False,
    but that won't always be true in writing proofs. We'll see a more
    complex version of [return] soon. *)

(** You will have noticed that in the proofs above we wrote [fun]
    with two placeholders in constructing our proofs. This is because
    both [forall] and [->] correspond to function types. [->] is just a
    shorthand for a degenerate use of [forall] where there is no
    dependency, i.e., no need to give a name to the type on the
    left-hand side of the arrow:

           forall (x:nat), nat
        =  forall (_:nat), nat
        =  nat -> nat

    Hence, [forall A, A -> True] is really [forall (A : Prop) (_ : A), True]
 *)

(** **** Exercise: 1 star, standard (A_then_A)

    As a definition, show that A implies A *)

Definition A_then_A : forall A, A -> A :=
  fun A x => x.

(** What does this correspond to computationally?

    [] *)


(** You're probably familiar with these basic rules of logic, but we
    can easily express them as definitions: *)

Definition modus_ponens {X Y : Prop} : (X -> Y) -> X -> Y :=
  fun f x => f x.

Definition chain_rule {X Y Z : Prop}  : (X -> Y) -> (Y -> Z) -> (X -> Z) :=
  fun fxy fyz x => fyz (fxy x).

(** Note that the chain rule is simply function composition. *)

(** **** Exercise: 1 star, standard (modus_tollens)

    Prove modus tollens definitionally *)

Definition modus_tollens {X Y : Prop} : (X -> Y) -> (Y -> False) -> (X -> False) :=
  fun f g x => g (f x).

(** [] *)

End functions.

(* ################################################################# *)
(** * Logical Connectives as Inductive Types *)

(** Inductive definitions are powerful enough to express most of
    the connectives we have seen so far.  Indeed, only universal
    quantification (with implication as a special case) is built into
    Rocq; all the others are defined inductively.

    We'll see how in this section. *)

(* ================================================================= *)
(** ** Conjunction *)

(** To prove that [P /\ Q] holds, we must present evidence for both
    [P] and [Q].  Thus, it makes sense to define a proof object for [P
    /\ Q] as consisting of a pair of two proofs: one for [P] and
    another one for [Q]. This leads to the following definition. *)

Module And.

Inductive and (P Q : Prop) : Prop :=
  | conj : P -> Q -> and P Q.

Arguments conj [P] [Q].

Notation "P /\ Q" := (and P Q) : type_scope.

(** Notice the similarity with the definition of the [prod] type,
    given in chapter [Poly]. The only difference is that [prod] takes
    [Type] arguments, whereas [and] takes [Prop] arguments. *)

Print and.
Print prod.
(* ===>
   Inductive prod (X Y : Type) : Type :=
   | pair : X -> Y -> X * Y. *)

(** This similarity should clarify why [destruct] can be used on a
    conjunctive hypothesis. Like [prod], [and] is an inductive
    datatype with only a single constructor. Hence, when we do case
    analysis, we only have one case to consider, in which we have
    terms (proofs) of A and B. *)

Theorem proj1' : forall P Q,
  P /\ Q -> P.
Proof.
  intros P Q HPQ. destruct HPQ as [HP HQ]. apply HP.
Defined.

Print proj1'.

(* Using [Defined] instead of [Qed] allows us to simplify the proof *)

Compute proj1'.

(** Similarly, the [split] tactic actually works for any inductively
    defined proposition with exactly one constructor.  In particular,
    it works for [and]: *)

Lemma and_comm' : forall P Q : Prop, P /\ Q -> Q /\ P.
Proof.
  intros P Q Hpq.
  destruct Hpq as [Hp Hq].
  split. (* = apply conj *)
  apply Hq.
  apply Hp.
Qed.

(** This shows why the inductive definition of [and] can be
    manipulated by tactics as we've been doing.  We can also use it to
    build proofs directly, using pattern-matching.  For instance: *)

Definition and_comm_if P Q (pq : P /\ Q) : Q /\ P :=
  match pq with
  | conj p q => conj q p
  end.

(* We can use the prior lemma to directly construct the bidirectional proof of
   and_comm as well: *)

Definition iff (A B : Prop) := (A -> B) /\ (B -> A).

Notation "A '<->' B" := (iff A B) : type_scope.

Definition and_comm P Q : P /\ Q <-> Q /\ P :=
  conj (and_comm_if P Q) (and_comm_if Q P).

(** **** Exercise: 1 star, standard (and_assoc')

    Construct a proof object (i.e. write a program) for [and] associativity. *)

Definition and_assoc' : forall P Q R, (P /\ Q) /\ R -> P /\ (Q /\ R)
   := fun P Q R H => 
    match H with
    | conj (conj p q) r => conj p (conj q r)
    end.
(** [] *)

(** **** Exercise: 2 stars, standard (conj_fact)

    Construct a proof object demonstrating the following proposition. *)

Definition conj_fact : forall P Q R, P /\ Q -> Q /\ R -> P /\ R :=
  fun P Q R HPQ HQR =>
    match HPQ, HQR with
    | conj p _, conj _ r => conj p r
    end.
(** [] *)

End And.

(* ================================================================= *)
(** ** Disjunction *)

Module Or.

(** The inductive definition of disjunction uses two constructors, one
    for each side of the disjunct. This corresponds to a _sum type_ in
    functional programming. *)

Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B.

Arguments inl {A B}.
Arguments inr {A B}.
Notation "P + Q" := (sum P Q) : type_scope.

(** A quick example of a sum type in functional programming: *)

Fixpoint remove_bools (l : list (nat + bool)) : list nat
(* WORKED IN CLASS *) :=
  match l with
  | [] => []
  | inl n :: l' => n :: remove_bools l'
  | inr _ :: l' => remove_bools l'
  end.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Arguments or_introl [P Q].
Arguments or_intror [P Q].

Notation "P \/ Q" := (or P Q) : type_scope.

(** This declaration explains the behavior of the [destruct] tactic on
    a disjunctive hypothesis, since the generated subgoals match the
    shape of the [or_introl] and [or_intror] constructors. *)

(** Once again, we can also directly write proof objects for theorems
    involving [or], without resorting to tactics. *)

Definition or_false_r : forall P, P \/ False -> P
  (* WORKED IN CLASS *)
  := fun _ p =>
  match p with
  | or_introl p' => p'
  | or_intror f  => match f with end
  end.

Definition or_elim : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R :=
  fun P Q R poq pr qr  =>
    match poq  with
    | or_introl p => pr p
    | or_intror q => qr q
    end.

Theorem or_elim' : forall (P Q R : Prop), (P \/ Q) -> (P -> R) -> (Q -> R) -> R.
Proof.
  intros P Q R poq pr qr.
  destruct poq as [p | q].
  - apply pr. apply p.
  - apply qr. apply q.
Qed.

(** **** Exercise: 2 stars, standard (or_comm)

    Construct a proof object for the following proposition. *)

Definition or_comm : forall P Q, P \/ Q -> Q \/ P :=
  fun P Q H =>
    match H with
    | or_introl p => or_intror p
    | or_intror q => or_introl q
    end.

(** [] *)

(** **** Exercise: 2 stars, standard (or_assoc)

    Write down an explicit proof object for [or_assoc]. *)

Definition or_assoc : forall P Q R, (P \/ Q) \/ R -> P \/ (Q \/ R)  :=
  fun P Q R H =>
    match H with
    | or_introl (or_introl p) => or_introl p
    | or_introl (or_intror q) => or_intror (or_introl q)
    | or_intror r            => or_intror (or_intror r)
    end.
(** [] *)

End Or.

(* ################################################################# *)
(** * Predicate Calculus and Dependent Types *)

(** So far, the logic we've expressed has been the simplest form of
    logic: Propositional Logic. In fact, we could write the proofs
    above in a simple polymorphic language like OCaml.

    To state more complicated propositions we will need _dependent types_.
    Consider the following inductive relations: *)

Inductive beautiful : nat -> Prop :=
| b2 : beautiful 2
| b4 : beautiful 4
| b8 : beautiful 8.

Inductive wonderous : nat -> Prop :=
| w8 : wonderous 8.

(** [beautiful] itself is not a proposition (or type), [beautiful 2]
    and [beautiful 3] are. That is, Rocq allows our Props (and our
    types) to depend on _terms_. This allows us to state, and attempt
    to prove, the following: *)

Definition beautiful2 : beautiful 2 := b2.
Fail Definition beautiful3 : beautiful 3 := b4.

(** In the second case we can state that three is beautiful, but we
    can't prove it. We can also try something more complex: *)

Definition wonderous_then_beautiful : forall n, wonderous n -> beautiful n :=
  fun n w => match w with
               w8 => b8
             end.

(** Note that the typechecker recognizes that in the only case of the match,
    n is 8. *)

Print wonderous_then_beautiful.
(* ==>
  fun (n : nat) (w : wonderous n) =>
  match w in (wonderous n0) return (beautiful n0) with
  | w8 => b8
  end
 *)

(** Note the [in] and [return] in the match statement.
    [in] assigns a name to the arguments in type of w: specifically,
    it calls the argument to [wonderous] "n0".
    [return] then specifies the return type, which may depend on the
    names assigned by [in].
    Hence, Rocq knows that it's trying to provide a [beautiful n0] for
    every [wonderous n0] and when [n0] is [8], the constructor [b8]
    suffices.

    Above Rocq inferred the relevant parts of the match statement,
    but that tends to occur only in trivial cases. *)

(** Most of the propositions we have looked at in this course use dependent
    types. Let's try to directly prove something about [ev]: *)

Print ev.
(* ==>
Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall n : nat, ev n -> ev (S (S n))
*)

Definition ev_plus_four : forall n, ev n -> ev (4 + n)
  (* WORKED IN CLASS *) :=
  fun n pf_n => ev_SS _ (ev_SS n pf_n).

(** **** Exercise: 2 stars, standard (ev_two)

    Write a program proving that two is even *)

Definition ev_two : ev 2
:= ev_SS 0 ev_0.
(** [] *)

(* ================================================================= *)
(** ** Existential Quantification *)

(** To give evidence for an existential quantifier, we package a
    witness [x] together with a proof that [x] satisfies the property
    [P]: *)

Module Ex.

Inductive ex {A : Type} (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.

(** In English, for any predicate [P], given an [x] and a term/proof
    of [P x], we can construct a term/proof of [ex P]. *)

(** Let's show that there is an x satisfying [ev]: *)

Definition something_is_even : ex ev := ex_intro ev 0 ev_0.

(* Exists has a bit of a funny notation that we can use: *)

Notation "'exists' x , p" := (ex (fun x => p)) (at level 200, x binder, right associativity).

Definition something_is_even' : exists x, ev x := ex_intro ev 0 ev_0.

Check ex (fun n => ev n) : Prop.

End Ex.


(* ################################################################# *)
(** * Equality *)

Module MyEquality.

(** Even Rocq's equality relation is not built in.  It has the
    following inductive definition. *)

Inductive eq {A : Type} : A -> A -> Prop :=
  | eq_refl : forall {a : A}, eq a a.

Notation "x = y" := (eq x y) (at level 70): type_scope.

(** Of course, there are other, arguably more useful ways to define
    equality.  Here's Leibniz's definition: *)

Definition eqL {A : Type} (a b : A) : Prop := forall (P : A -> Prop), P a -> P b.

Notation "x =L y" := (eqL x y) (at level 70): type_scope.

(** That is, 'a' is equal to 'b' if everything true of 'a' is true of
    'b'. *)

(** Let's show that eqL is at least as strong as eq. *)

Lemma eqL_then_eq : forall (A : Type) (a b : A), a =L b -> a = b.
Proof.
  (* WORKED IN CLASS *)
  intros A a b L.
  unfold eqL in L.
  apply L.
  apply eq_refl.
Qed.

(** This is actually easier to express definitionally, if harder to
    come up with. *)

Definition eqL_then_eq' (A : Type) (a b : A) (PLe : a =L b) : a = b :=
  PLe (fun x => a = x) eq_refl.

Print eqL_then_eq.

(** Let's try going in the opposite direction. *)

Lemma eq_then_eqL : forall (A : Type) (a b : A), a = b -> a =L b.
Proof.
  intros A a b H.
  unfold eqL.
  intros P pf.
  destruct H.
  apply pf.
Qed.

Definition eq_then_eqL' : forall (A : Type) (a b : A), a = b -> a =L b
  (* WORKED IN CLASS *) :=
  fun A a b H => match H with
              | @eq_refl _ a' => fun P pf => pf
              end.


Print eq_then_eqL.

(** For convenience, we can package these up into a single claim. *)

Definition eq_eqL (A : Type) (a b : A) : a = b <-> a =L b :=
  conj (eq_then_eqL A a b) (eqL_then_eq A a b).

(** What does this tell us? It says that it's okay to replace a with b
    throughout a proposition if we know that [eq a b]. Let's try it
    out. *)

Lemma eq_2_beautiful : forall (x : nat), 2 = x -> beautiful x.
Proof.
  (* WORKED IN CLASS *)
  intros x H.
  apply (eq_then_eqL _ _ _ H).
  apply b2.
Qed.

(** **** Exercise: 1 star, standard (eq_trans')

    Exercise: Prove transitivity using our version of eq, which doesn't have
    [rewrite]. **)

Lemma eq_trans' : forall (A : Type) (a b c : A),  a = b -> b = c -> a = c.
Proof.
  intros A a b c H1 H2.
  destruct H1.
  destruct H2.
  exact eq_refl.
Qed.
(** [] *)

End MyEquality.

(* ################################################################# *)
(** * Interlude: Dependent Types and Programming in the Proof Environment *)

Module ilist.

(** You might be wondering: Given that we can write types in Rocq that
    depend on terms, are there any interesting (non-proof) datatypes we can
    write?

    The answer is yes! We can write a variety of interesting datatypes in
    Rocq that prevent common programming errors!

    For instance, here's a length-indexed list: *)

Inductive ilist (X : Type) : nat -> Type :=
| inil : ilist X 0
| icons (n : nat) (x : X) (l : ilist X n) : ilist X (S n).

Arguments inil {X}.
Arguments icons {X n}.

Notation "x ::: l" := (icons x l)
                      (at level 60, right associativity).
Notation "[[ ]]" := inil.
Notation "[[ x ; .. ; y ]]" := (icons x .. (icons y inil) ..).

Definition ihd {X n} (l : ilist X (S n)) : X :=
  match l with
  | x ::: l => x
  end.

(** Unfortunately, Rocq isn't great at recognizing impossible cases: *)

Fail Fixpoint izip {X Y n} (l1 : ilist X n) (l2 : ilist Y n) : ilist (X * Y) n :=
  match l1, l2 with
  | [[]]      , [[]]     => [[]]
  | x ::: xs, y :: ys => (x,y) ::: (izip xs ys)
  end.

(** This is where the proof assistant comes in handy. *)

Fixpoint izip {X Y n} (l1 : ilist X n) (l2 : ilist Y n) : ilist (X * Y) n.
  destruct l1 as [|n x xs].
  - apply inil.
  - inversion l2 as [|? y ys]; subst.
    apply icons.
    apply (x,y).
    apply (izip _ _ n xs ys).
Defined.

(** Note that we ended our definition with [Defined].
    [Qed] makes a definition _opaque_, meaning that we can't read it off.
    This is fine for proofs, but not very desirable for functions that
    we intend to run. *)

Print izip.

(** **** Exercise: 2 stars, standard, optional (ilastn)

    Use the proof environment to get the last n elements of an m + n ilist.  *)

Fixpoint ilastn {X} (m n : nat) (l1 : ilist X (m + n)) : ilist X n.
(* FILL IN HERE *) Admitted.

Example test_ilastn1: ilastn 2 3 [[ 2; 5; 8; 11; 14]] = [[ 8; 11; 14 ]].
(* FILL IN HERE *) Admitted.
Example test_ilastn2: forall x y, ilastn 1 4 [[ x; 2; 1; y; 3]] = [[ 2; 1 ; y ; 3 ]].
(* FILL IN HERE *) Admitted.

(** [] *)

(** **** Exercise: 2 stars, advanced (ireverse)

    Write a function to reverse an ilist.

    Hint: You probably need an auxiliary function. *)

(* FILL IN HERE *)
Fixpoint isnoc {X n} (l : ilist X n) (x : X) : ilist X (S n) :=
  match l with
  | inil => [[ x ]]
  | h ::: t => h ::: (isnoc t x)
  end.

(* Main reverse function *)
Fixpoint ireverse {X n} (l : ilist X n) : ilist X n :=
  match l with
  | inil => inil
  | h ::: t => isnoc (ireverse t) h
  end.

(* FILL IN HERE *)

Example test_ireverse1: ireverse [[ 2; 5; 8; 11; 14]] = [[ 14; 11; 8; 5; 2]].
Proof. reflexivity. Qed.
Example test_ireverse2: ireverse [[ 2; 5; 2; 3]] = [[ 3; 2; 5; 2]].
Proof. reflexivity. Qed.
(** [] *)

End ilist.

(** **** Exercise: 4 stars, standard, optional (bst)

    Implement a dependently typed binary search tree and an efficient
    [element_in] procedure.

    Prove that if an element is in the tree, the procedure finds it. *)

(** [] *)

(* ################################################################# *)
(** * Rocq's Trusted Computing Base *)

(** One issue that arises with any automated proof assistant is
    "why trust it?": what if there is a bug in the implementation that
    renders all its reasoning suspect?

    While it is impossible to allay such concerns completely, the fact
    that Rocq is based on the Curry-Howard correspondence gives it a
    strong foundation. Because propositions are just types and proofs
    are just terms, checking that an alleged proof of a proposition is
    valid just amounts to _type-checking_ the term.  Type checkers are
    relatively small and straightforward programs, so the "trusted
    computing base" for Rocq -- the part of the code that we have to
    believe is operating correctly -- is small too.

    What must a typechecker do?  Its primary job is to make sure that
    in each function application the expected and actual argument
    types match, that the arms of a [match] expression are constructor
    patterns belonging to the inductive type being matched over and
    all arms of the [match] return the same type, and so on. *)

(** There are a few additional wrinkles:

    First, since Rocq types can themselves be expressions, the checker
    must normalize these (by using the computation rules) before
    comparing them.

    Second, the checker must make sure that [match] expressions are
    _exhaustive_.  That is, there must be an arm for every possible
    constructor.  To see why, consider the following alleged proof
    object: *)

Fail Definition or_bogus : forall P Q, P \/ Q -> P :=
  fun (P Q : Prop) (pq : P \/ Q) =>
    match pq with
    | or_introl p => p
    end.

(** All the types here match correctly, but the [match] only
    considers one of the possible constructors for [or].  Rocq's
    exhaustiveness check will reject this definition.

    Third, the checker must make sure that each recursive function
    terminates.  It does this using a syntactic check to make sure
    that each recursive call is on a subexpression of the original
    argument.  To see why this is essential, consider this alleged
    proof: *)

Fail Fixpoint infinite_loop {X : Type} (n : nat) {struct n} : X :=
  infinite_loop n.

Fail Definition falso : False := infinite_loop 0.

(** Recursive function [infinite_loop] purports to return a
    value of any type [X] that you would like.  (The [struct]
    annotation on the function tells Rocq that it recurses on argument
    [n], not [X].)  Were Rocq to allow [infinite_loop], then [falso]
    would be definable, thus giving evidence for [False].  So Rocq rejects
    [infinite_loop]. *)

(** Note that the soundness of Rocq depends only on the
    correctness of this typechecking engine, not on the tactic
    machinery.  If there is a bug in a tactic implementation (and this
    certainly does happen!), that tactic might construct an invalid
    proof term.  But when you type [Qed], Rocq checks the term for
    validity from scratch.  Only theorems whose proofs pass the
    type-checker can be used in further proof developments.  *)

(* 2026-02-02 23:09 *)
