Require Import CpdtTactics.
Require Import List.

Set Implicit Arguments.
Obligation Tactic := crush.



Definition thunk (n : nat) (a : Type) := a.
Definition tick (n : nat) (T : Type) (t : thunk n T) : thunk (S n) T := t.
Definition ret (T : Type) (a : T) : thunk 0 T := a.
Definition force  (n : nat) (T : Type) (t : thunk n T) : T := t.
Definition bind (n m : nat) (a b : Type) (t : thunk n a) (f : a -> thunk m b) : thunk (n+m) b :=
  f t.
Definition rbind (n m : nat) (a b : Type) (f : a -> thunk m b) (t : thunk n a) : thunk (n+m) b :=
  f t.
Definition wait (n m : nat) (T : Type) (a : thunk n T) : thunk (1+n+m) T := a.
Definition returnw (n : nat) (T : Type) (a : T) : thunk (1+n) T := a.
Definition ifthenelse (T : Type) (q : bool) (a : T) (b : T) := if q then a else b.
Definition pay (n m : nat) (T : Type) (a : thunk n T) : thunk m (thunk (n-m) T) := a.


Implicit Arguments tick [[n] [T]].
Implicit Arguments ret [[T]].
Implicit Arguments force [[n] [T]].
Implicit Arguments bind [[m] [n] [a] [b]].
Implicit Arguments rbind [[m] [n] [a] [b]].
Implicit Arguments wait [[n] [T]].
Implicit Arguments pay [[n] [T]].


Infix ">>=" := bind (at level 50).
Infix "=<<" := rbind (at level 50).
Notation "./" := tick.

(*Example: show that appending two lists takes time linear in the output*)
Inductive Seq (T : Type) : nat -> Type :=
  Nil : Seq T 0
| Cons : forall n, T -> Seq T n -> Seq T (S n).
Infix "::" := Cons.
Notation "[]" := Nil.



Eval compute in (ret (3::(Nil nat))) >>= (fun x => ./ (ret (4::x))).

Fixpoint sapp (T : Type) (n m : nat) (s1 : Seq T n) (s2 : Seq T m)
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

Fixpoint snoc (T : Type) (t : T) (q : Q T)  : thunk 5 (Q T) :=
  match q with
    | empty => ./ (returnw 3 (single t))
    | single  t1          => ./ (returnw 3 (twoZero t t1 (returnw 4 (empty (T*T)))))
    | twoZero t1 t2 q'    => ./ (pay 2 q' >>= (fun q => ./ (returnw 0 (twoOne t1 t2 q t))))

    | twoOne  t1 t2 q' t3 => ./ q' >>= (fun q => ./ (ret (twoZero t1 t2 (snoc (t3, t) q))))

    | oneZero t1    q'    => ./ (returnw 3 (twoZero t t1 q'))

    | oneOne  t1    q' t2 => ./ (pay 3 (snoc (t, t2) q') >>= 
      (fun q => ./ (returnw 0 (oneZero t1 q))))
 end.

Eval compute in snoc 8 (snoc 7 (snoc 6 (snoc 5 (snoc 3 (snoc 4 (empty nat)))))).

Inductive ViewQL (T : Type) := 
| nilView : ViewQL T
| consView : T -> thunk 4 (Q T) -> ViewQL T.

Definition expand1 (T : Type) (q : ViewQL (T*T)) : thunk 1 (Q T) :=
  match q with
    | nilView => ./ (ret (empty T))
    | consView (a1, a2) q' =>  ./ (ret (twoZero a1 a2 (wait 0 q')))
  end.

Definition expand2 (T : Type) (x1 : T) (x2 : T) (q : ViewQL (T*T)) : thunk 1 (Q T) :=
  match q with
    | nilView => ./ (returnw 1 (single x2))
    | consView (a1, a2) q' =>  ./ (pay 1 q' >>= (fun q'' => ret (twoOne a1 a2 q'' x2)))
  end.


Fixpoint view (T : Type) (q : Q T) : thunk 1 (ViewQL T) :=
  match q with
    | empty => ./ (ret (nilView T))
    | single  t1          => ./ (ret (consView t1 (returnw 3 (empty T))))
    | twoZero t1 t2 q'    => ./ (ret (consView t1 ((pay 3 q') >>= (fun q => ./ (ret (oneZero t2 q))))))
    | twoOne  t1 t2 q' t3 => ./ (ret (consView t1 (q' >>= (fun q => ./ (ret (oneOne t2 q t3))))))
    | oneZero t1    q'    => ./ (ret (consView t1 ((q' >>= @view (T*T)) >>= (@expand1 T))))
    | oneOne  t1    q' t2 => ./ (ret (consView t1 (view q' >>= (expand2 t1 t2))))
  end.

