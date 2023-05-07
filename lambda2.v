Import Nat.
Require Import List.
Import List.ListNotations.

Definition atomic_type := nat.

Inductive type : Type :=
| Var : atomic_type -> type
| Arr : type -> type -> type
| Pi : atomic_type -> type -> type.

Notation "& x" := (Var x) (at level 8).
Infix ">>" := Arr (right associativity, at level 9).

Fixpoint FVb (n : atomic_type) (t : type) : bool :=
  match t with
  | &m => eqb n m
  | a >> b => (FVb n a) || (FVb n b)
  | Pi m t => (negb (eqb m n)) && (FVb n t) 
  end.

Fixpoint FVl (t : type) : list atomic_type :=
  match t with
  | &m => [m]
  | a >> b => (FVl a) ++ (FVl b)
  | Pi m t => remove PeanoNat.Nat.eq_dec m (FVl t)
  end.

Definition atomic_term := nat.

Inductive term : Type :=
| TVar : atomic_term -> term
| App : term -> term -> term
| Tapp : term -> type -> term
| Abs : atomic_term -> type -> term -> term
| Tabs : atomic_type -> term -> term.

Notation "# x" := (TVar x) (at level 10).
Infix "!" := (App) (left associativity, at level 11).
Infix "!!" := (Tapp) (left associativity, at level 12).
Notation "\ x t m" := (Abs x t m) (right associativity, at level 13).
Notation "/ t m" := (Tabs t m) (right associativity, at level 14).

Inductive statement : Type :=
| St : term -> type -> statement
| TSt : type -> statement.

Infix ":#" := St (at level 10).

Inductive declaration : Type :=
| Std : atomic_term -> type -> declaration
| TStd : atomic_type -> declaration.

Infix ":*" := Std (at level 10).

Definition context := list declaration.

Fixpoint check_type (G : context) (t : atomic_type) : bool :=
  match G with
  | nil => false
  | cons d G' =>
    match d with
    | _ :* _ => check_type G' t
    | TStd n => eqb n t || check_type G' t
    end
  end.

Fixpoint check_term (G : context) (x : atomic_term) : bool :=
  match G with
  | nil => false
  | cons d G' =>
    match d with
    | y :* _ => eqb x y || check_term G' x
    | TStd _ => check_term G' x
    end
  end.

Definition foreach {T : Type} (l : list T) (P : T -> bool) := fold_left andb (map P l) true = true.

Coercion atomic_type_as_declaration (a : atomic_type) : declaration := TStd a.

Inductive l2_context : context -> Prop :=
| Emp : l2_context []
| CType : forall (G : context) (a : atomic_type), l2_context G -> (check_type G a = false) -> l2_context ((TStd a) :: G)
| CTerm : forall (G : context) (x : atomic_term) (r : type), l2_context G -> (check_term G x = false) -> (foreach (FVl r) (check_type G)) -> l2_context ((x :* r) :: G).


Fixpoint subs (t : type) (a : atomic_type) (b : type) : type :=
  match t with
  | & x => if eqb x a then b else t
  | r >> s => (subs r a b) >> (subs r a b)
  | Pi x s => if eqb x a then t else Pi x (subs s a b)
  end.

Coercion atomic_term_as_term (a : atomic_term) : term := # a.

Reserved Notation "G ⊢ st" (no associativity, at level 61). (* 22a2 *)

Inductive l2 : context -> statement -> Prop :=
| Var2 : forall (G : context) (x : atomic_term) (s : type), (l2_context G) -> (In (x :* s) G) -> G ⊢ x :# s
| App2 : forall G M N s t, (G ⊢ (M :# (s >> t))) -> (G ⊢ (N :# s)) -> G ⊢ ((M ! N ) :# t)
| Abs2 : forall G M x s t, ((x :* s) :: G ⊢ M :# t) -> G ⊢ (Abs x s M) :# (s >> t)
| Form2 : forall G B, (l2_context G) -> (foreach (FVl B) (check_type G)) -> G ⊢ TSt B
| Tapp2 : forall G M a A B, (G ⊢ (M :# (Pi a A))) -> (G ⊢ (TSt B)) -> G ⊢ ((M !! B) :# (subs A a B))
| Tabs2 : forall G a M A, ((TStd a)::G ⊢ M :# A) -> G ⊢ (Tabs a M) :# (Pi a A)
where "G ⊢ st" := (l2 G st).

Lemma context_term : forall G x s, l2_context ((x :* s) :: G) -> l2_context G.
Proof. intros G x s H. inversion H. auto. Qed.