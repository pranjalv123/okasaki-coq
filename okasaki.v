Require Import CpdtTactics.
Require Import List.

Set Implicit Arguments.
Obligation Tactic := crush.



Definition thunk (n : nat) (a : Type) := a.
Definition tick (n : nat) (T : Type) (t : thunk n T) := t.
Definition ret (T : Type) (a : T) := a.
Definition force  (n : nat) (T : Type) (t : thunk n T) := t.
Definition bind (n m : nat) (a b : Type) (t : thunk n a) (f : a -> thunk m b) :=
  f t.
Definition rbind (n m : nat) (a b : Type) (f : a -> thunk m b) (t : thunk n a) :=
  f t.
Definition wait (n m : nat) (T : Type) (a : T) := a.
Definition returnw (n : nat) (T : Type) (a : T) := a.
Definition ifthenelse (T : Type) (q : bool) (a : T) (b : T) := if q then a else b.
Definition pay (n m : nat) (T : Type) (a : T) := a.

Infix ">>=" := bind (at level 50).
Infix "=<<" := rbind (at level 50).
Notation "./" := tick.

(*Example: show that appending two lists takes time linear in the output*)
Inductive Seq (T : Type) : nat -> Type :=
  Nil : Seq T 0
| Cons : forall n, T -> Seq T n -> Seq T (S n).
Infix "::" := Cons.
Notation "[]" := Nil.

Eval compute in  (ret (4::(3::(2::(Nil nat))))).

Program Fixpoint sapp (T : Type) (n m : nat) (s1 : Seq T n) (s2 : Seq T m)
  : thunk (1+n+n) (Seq T (n+m)) :=
    match s1 in (Seq _ n) return thunk (1+n+n) (Seq T (n+m)) with
      | Nil => ./ (ret s2)
      | s::s1' => ./ ((sapp s1' s2) >>= (fun xs => ./ (ret (s::xs))))
    end.
Print Assumptions sapp. (* No assumptions *)

Infix "++" := sapp.


Inductive Q (T : Type) := 
| empty : Q T
| single : T -> Q T
| twoZero : T -> T -> thunk 5 (Q (T*T)) ->      Q T
| twoOne :  T -> T -> thunk 3 (Q (T*T)) -> T -> Q T
| oneZero : T ->      thunk 2 (Q (T*T)) ->      Q T
| oneOne  : T ->               Q (T*T)  -> T -> Q T.

Axiom cheat:forall T, T.

Fixpoint snoc (T : Type) (t : T) (q : Q T) {struct q} : thunk (Q T) 5 :=
  match q with
    | empty => ./ (returnw 3 (single t))
    | single  t1          => ./ (returnw 3 (twoZero t t1 (returnw 4 (empty (T*T)))))
    | twoZero t1 t2 q'    => ./ (pay 2 q' >>= (fun q => ./ (returnw 0 (twoOne t1 t2 q t))))

    | twoOne  t1 t2 q' t3 => ./ q' >>= (fun q => ./ (ret (twoZero t1 t2 (snoc (t3, t) q))))

    | oneZero t1    q'    => cheat _(*./ (returnw 3 (twoZero t t1 q'))*)

    | oneOne  t1    q' t2 => cheat _ (*./ (pay 3 (snoc (t, t2) q') >>= 
                                    (fun q => ./ (returnw 0 (oneZero t1 q))))*)
 end.


Program Fixpoint len (T : Type) (q : Q T) : nat :=
  match q with
    | empty            => 0
    | single  _        => 1
    | twoZero _ _ q'   => 2 + (fmap len q')
    | twoOne  _ _ q' _ => 3 + (fmap len q')
    | oneZero _   q'   => 1 + (fmap len q')
    | oneOne  _   q' _ => 2 + (fmap len q')
  end.
        