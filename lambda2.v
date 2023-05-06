Import Nat.
Require Import List.
Import List.ListNotations.

Definition atomic_type := nat.

Inductive type : Type :=
| Var : atomic_type -> type
| Arr : type -> type -> type
| Pi : atomic_type -> type -> type.

Notation "& x" := (Var x) (at level 10).
Infix ">>" := Arr (right associativity, at level 11).

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
| Abs : atomic_term -> type -> term
| Tabs : atomic_type -> term.

Notation "# x" := (TVar x) (at level 10).
Notation "* a b" := (App a b) (left associativity, at level 11).
Notation "^ a b" := (Tapp a b) (left associativity, at level 12).
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
| Emp : forall (G : context), (G = nil) -> l2_context G
| CType : forall (G : context) (a : atomic_type), (check_type G a = false) -> l2_context ((TStd a) :: G)
| CTerm : forall (G : context) (x : atomic_term) (r : type), (check_term G x = false) -> (foreach (FVl r) (check_type G)) -> l2_context ((x :* r) :: G).