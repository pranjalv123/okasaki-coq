Require Import CpdtTactics.
Require Import List.
Require Import Arith.

Set Implicit Arguments.
Obligation Tactic := crush.

Inductive thunk : nat -> Type -> Type :=
| ret : forall T, T -> thunk 0 T
| tick : forall n T, thunk n T -> thunk (S n) T
| bind : forall T a n m, thunk n a -> (a -> thunk m T) -> thunk (n+m) T.

Fixpoint wait T (n m : nat) (t : thunk n T) : thunk (m+n) T := 
  match m return thunk (m+n) T with
    | 0    => t
    | S m' => tick (wait m' t)
  end.

Fixpoint force n T (t : thunk n T) : T :=
  match t with
    | ret _ a => a
    | tick _ _ a => force a
    | bind _ _ _ _ t f => force (f (force t))
  end.

(*
Definition pay (n m : nat) (T : Type) (t : thunk (n+m) T) : thunk m (thunk (n) T)
  match t with
    | ret _ a => ret (ret a)
    | tick _ a => 
*)
(*Definition rbind (n m : nat) (a b : Type) (f : a -> thunk m b) (t : thunk n a) : thunk (n+m) b := bind f 
Definition wait (n m : nat) (T : Type) (a : thunk n T) : thunk (1+n+m) T := a.
Definition returnw (n : nat) (T : Type) (a : T) : thunk (1+n) T := a.
Definition ifthenelse (T : Type) (q : bool) (a : T) (b : T) := if q then a else b.




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
*)
Inductive Stream (T : Type) : nat -> Type := 
| SNil : Stream T 0
| SCons : forall m, T -> thunk 1 (Stream T m) -> Stream T (S m).


Fixpoint StrApp (T : Type) (n m : nat) (s1 : Stream T n) (s2 : Stream T m) : thunk (n+n+1)(Stream T (n+m)) :=
  match s1 in (Stream _ n) return thunk (n+n+1) (Stream T (n+m)) with 
    | SNil => ./ (ret s2)
    | SCons _ a s1'  => (StrApp s1' s2) >>= (fun x => ./ (ret (SCons a x)))
  end.

Eval compute in SCons 3 (SNil nat).

Check refl_equal nat.


Lemma rev_mk : forall (m n' : nat) (T : Type), thunk (1 + (1 + S m + n')) (Stream T (S m + n')) -> thunk (1 + m + S (S n')) (Stream T (m + S n')).
  intros.
  Lemma rev_eq : forall (m n' : nat) (T : Type), thunk (1 + (1 + S m + n')) (Stream T (S m + n')) = thunk (1 + m + S (S n')) (Stream T (m + S n')).
    intros; f_equal; crush.
  Qed.
  rewrite rev_eq in X.
  trivial.
Qed.

Fixpoint revhelper (T : Type) (n m : nat) (s1 : Stream T n) (s2 : Stream T m) :
   (Stream T (m+n)):=
  match s1 with 
    | SCons (n') a s1' =>  ./(rev_mk (s1' >>= (fun x => ./(revhelper x (SCons a s2)))))
    | SNil => ./ (StrApp s2 (SNil T))
  end.
  

Fixpoint StrRev (T : Type) (n : nat) (s1 : Stream T n) : (Stream T n) := 
  revhelper s1 (SNil T).
Eval compute in (StrRev (SCons 1 (SCons 2 (SCons 3 (SCons 4 (SNil nat)))))).

Inductive BankerQ (T : Type) (n : nat) :=
| bq : forall f , n >= f -> Stream T f -> Stream T (n-f) -> BankerQ T n.

Check bq.
Print Implicit bq.

Program Definition BQempty (T : Type) := bq (n:=0) _ (SNil T) (SNil T).

Lemma three_ge_two : 3 >= 2. crush. Qed.
Eval compute in bq three_ge_two (SCons 4 (SCons 3 (SNil nat))) (SCons 2 (SNil nat)).

Fixpoint stream_less_eq (T : Type) (n m : nat) (s1 : Stream T n) (s2 : Stream T m) : bool :=
  match s1, s2 with
    | SNil, _ => true
    | _, SNil => false
    | SCons n' a s1', SCons m' b s2'  => stream_less_eq s1' s2'
  end.

Lemma check_mk : forall T n n0, Stream T 0 -> Stream T (n - (n0 + (n - n0))).
  Lemma check_eq : forall T n n0, Stream T 0 = Stream T (n - (n0 + (n - n0))).
    crush.
  Qed.
  intros; rewrite <- check_eq; crush.
Qed.

Implicit Arguments check_mk [[T] [n] [n0]].
Print Implicit check_mk.

Program Definition check (T : Type) (n: nat) (q : BankerQ T n) : BankerQ T n  :=
  match q with 
    | bq _ pf fs rs => 
      match stream_less_eq fs rs with
        | true =>  q
        | false => bq _ (StrApp fs (StrRev rs)) (check_mk (SNil T))
      end
  end.
Obligation Tactic := eauto.
Program Definition bq_snoc (T : Type) (a : T) (n : nat) (q : BankerQ T n) : BankerQ T (S n) :=
  match q with
    | bq _ _ fs rs => check (bq _ fs (SCons a rs))
  end.
Obligation 2. 
  intros.
  induction wildcard'; crush.
Qed.

Check bq.

Definition bq_head (T : Type) (n : nat) (q : BankerQ T (S n)) :=
  match q return (match q with
                    | bq 0 _ _ _ => unit 
                    | bq (S n') _ _ _  => T
                  end) with 
    | bq 0 _ _ _ => tt
    | bq (S n') _ fs rs => match fs with
                             | SCons _ a _ => a
                             | SNil => tt
                      end
  end.

Print Implicit bq.

Lemma ge_minus_one : forall n m : nat, (S n) >= (S m) -> n >= m. crush. Qed.
Check SCons.

Definition bq_tail (T : Type) (n : nat) (q : BankerQ T (S n)) :  thunk 4 (BankerQ T n) :=
  match q return match q with  
                   | bq 0 _ f _ => unit
                   | bq (S m) _ f _ =>
                     match f with 
                       | SCons _ _ _ => BankerQ T n
                       | SNil => unit
                     end
                 end with
    | bq (S n') pf fs rs => match fs with
                              | SCons _  _ fs' =>  fs' >>= (fun x => check (bq _ x rs))
                              | SNil => tt
                            end
    | bq 0 _ _ _ => tt
                      
  end.


Inductive BootQ (T : Type) :=
| boote : BootQ T
| bootq : nat -> list T ->  BootQ (list T) -> nat -> list T -> BootQ T.

Check tl.

Fixpoint checkQ (T : Type) (q : BootQ T) : BootQ T :=
  match q with
    | boote => boote T
    | bootq lenfm f m lenr r => match lenr - lenfm with
                                    | 0 => checkF q
                                    | S p => bootq (lenfm+lenr) f (bootsnoc m (rev r)) 0 nil
                                end
    end
with checkF (T : Type) (q : BootQ T) :=
  match q with 
    | boote => boote T
    | bootq lenfm nil m lenr r => bootq lenfm (boothead m) (boottail m) lenr r
    | x => x
  end
with bootsnoc (T : Type) (q : BootQ T) (x : T) : BootQ T :=
  match q with
    | boote => bootq 1 (cons x nil) (boote (list T)) 0 nil
    | bootq lenfm f m lenr r => checkQ (bootq lenfm f m (lenr+1) (cons x r))
  end
with boothead (T : Type) (q : BootQ T) : T := 
  match q with 
    | boote => _
    | bootq _ (cons x f') _ _ _ => x
    | bootq _ nil _ _ _ => _
  end
with boottail (T : Type) (q : BootQ T) : BootQ T :=
  match q with 
    | boote => _
    | bootq lenfm (cons x f') m lenr r => checkQ (bootq (lenfm-1) f' m lenr r)
    | bootq _ nil _ _ _ => _
  end.