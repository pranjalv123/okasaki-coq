Require Import CpdtTactics.
Require Import List.
Require Import Arith.

Set Implicit Arguments.
Obligation Tactic := crush.

Record thunk (n : nat) (T : Type) :=
  Thunk {force : T}.

Definition setn n T (t : thunk n T) m := Thunk m (force t).
Definition tick n T (t : thunk n T) := setn t (S n).

Definition wait T (n m : nat) (t : thunk n T) : thunk (m+n) T := setn t (m+n).

Definition bind T a n m (t : thunk n a) (f : a -> thunk m T) : thunk (n+m) T := 
  setn (f (force t)) (n+m).


Definition pay (n m : nat) (T : Type) (t : thunk n T) : thunk m (thunk (n-m) T) :=
  Thunk m (setn t (n-m)).

Definition rbind (n m : nat) (a b : Type) (f : a -> thunk m b) (t : thunk n a) : thunk (n+m) b := bind t f.

Definition returnw (n : nat) (T : Type) (a : T) : thunk (1+n) T := Thunk (1+n) a.
Definition returnw' (n : nat) (T : Type) (a : T) : thunk (n) T := Thunk (n) a.
Definition ret (T : Type) (a : T) : thunk 0 T := Thunk 0 a.


Ltac makecast :=   
  intros; f_equal; crush;
  match goal with 
    | [H : ?a |- ?x] => assert (a = x); f_equal; crush
  end.


(*Implicit Arguments tick [[n] [T]].
Implicit Arguments ret [[T]].
Implicit Arguments force [[n] [T]].
Implicit Arguments bind [[m] [n] [a] [b]].
Implicit Arguments rbind [[m] [n] [a] [b]].
Implicit Arguments wait [[n] [T]].
Implicit Arguments pay [[n] [T]].*)


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

Program Fixpoint sapp (T : Type) (n m : nat) (s1 : Seq T n) (s2 : Seq T m)
  : thunk (2+n+n) (Seq T (n+m)) :=
    match s1 in (Seq _ n) return thunk (2+n+n) (Seq T (n+m)) with
      | Nil => ./ (returnw 0 s2)
      | s::s1' => ./ ((sapp s1' s2) >>= (fun xs => ./ (ret (s::xs))))
    end.
Obligation 1. fold plus; crush. Qed.
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

    | oneZero t1    q'    => ./ (returnw 3 (twoZero t t1 (wait 3 q')))

    | oneOne  t1    q' t2 => ./ (pay 3 (snoc (t, t2) q') >>= 
      (fun q => ./ (ret (oneZero t1 q))))
 end.

Inductive ViewQL (T : Type) := 
| nilView : ViewQL T
| consView : T -> thunk 4 (Q T) -> ViewQL T.

Definition expand1 (T : Type) (q : ViewQL (T*T)) : thunk 1 (Q T) :=
  match q with
    | nilView => ./ (ret (empty T))
    | consView (a1, a2) q' =>  ./ (ret (twoZero a1 a2 (wait 1 q')))
  end.

Definition expand2 (T : Type) (x1 : T) (x2 : T) (q : ViewQL (T*T)) : thunk 3 (Q T) :=
  match q with
    | nilView => ./ (returnw 1 (single x2))
    | consView (a1, a2) q' =>  ./ (pay 1 q' >>= (fun q'' => ./ (ret (twoOne a1 a2 q'' x2))))
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

Inductive Stream (T : Type) : nat -> nat -> Type := 
| SNil : forall k, Stream T k 0
| SCons : forall k m, T -> thunk k (Stream T k m) -> Stream T k (S m).


Lemma app_mk : forall T m, thunk (1 + 2) (Stream T 3 m) -> thunk 3 (Stream T 3 (0 + m)). 
  crush. Qed.


Definition StrTail (T : Type) (n k : nat) (s1 : Stream T k (S n)) : thunk k (Stream T k n) :=
  match s1  with 
    | SNil _ => tt
    | SCons _ _ _ s1' => s1'
  end.
Definition StrHead (T : Type) (n k : nat) (s1 : Stream T k (S n)) : T :=
  match s1 with 
    | SNil _ => tt
    | SCons _ _ a _ => a
  end.

Program Fixpoint StrApp (T : Type) (n m k : nat) (s1 : Stream T k n) (s2 : Stream T (2+k) m)
  : thunk (2+k) (Stream T (2+k) (n+m)) :=
  match s1 with
    | SCons k n' a s1' =>./(s1' >>= (fun x =>./( ret (SCons a (StrApp x s2)))))
    | SNil k => returnw (1+k) s2
  end.
  

Lemma rev_mk :  forall n' m k k' T, thunk k' (Stream T k (n' + S m)) -> thunk k' (Stream T k (S n' + m)). makecast. Qed.

Program Fixpoint revhelper (T : Type) (n m k : nat) (s1 : Stream T k n) (s2 : Stream T k m) { struct n} :
   thunk (2+2*n+n*k) (Stream T k (n+m)):=
  match n with
    | 0 => ./ (returnw 0 s2)
    | S n' => ./ ((StrTail s1) >>= (fun x => ./(rev_mk  n' m (revhelper (n:=n') x (SCons (StrHead (n:=(n')) s1) (returnw' k s2))))))
  end.
Obligation 3. fold plus. crush. Qed.

Lemma rev_mk' : forall n k T, thunk (2 + 2 * n + n * k) (Stream T k (n + 0)) -> thunk (2 + 2 * n + n * k) (Stream T k n). makecast. Qed.

Program Definition StrRev (T : Type) (n k: nat) (s1 : Stream T k n) : thunk (2+2*n+n*k) (Stream T k n) :=
  rev_mk' n (revhelper s1 (SNil T k)).


Print Implicit StrRev.
Check StrRev.
Check StrApp.
(*3*rs + 3*fs*)

Program Definition StrAppT T (n m a k b : nat) (s1 : thunk a (Stream T k n)) (s2 : thunk b (Stream T (2+k) m)) : thunk (5+a+b+k) (Stream T (2+k) (n+m)) :=
./(  s1 >>= (fun x => ./(s2 >>= fun y => ./ (StrApp x y)))).
Obligation 1.
fold plus. crush. Qed.

Check StrAppT.
Infix "++" := StrAppT.

Inductive BankerQ (T : Type) :  nat -> Type :=
| bq : forall a b, Stream T 2 a -> thunk (2+2*b) (Stream T 0 b) -> Stream T 0 b -> BankerQ T (a+2*b).
Check bq.
Print Implicit bq.

Program Definition emptybq T := bq (SNil T 2) (returnw 1 (SNil T 0)) (SNil T 0).


Program Definition makebq (T : Type) (a b c : nat) (s1 : Stream (thunk 1 T) a) 
  (s2 : Stream (thunk 0 T) b) (s3 : Stream (thunk 3 T) (c+d)) (s4 : Stream (thunk 0 T) c) :
  thunk 11 (BankerQ T (a+b+c+d+c))  :=
  match c with
    | 0 => (bq s1 s2 (StrRev s4) SNil )
    | S k'  => returnw (10) (bq s1 s2 s3 s4)
  end.

Implicit Arguments makebq [[T]].
Print bq.

Lemma snoc1 : forall T r k k', k = (S k') -> thunk (k + k + k - 3) (Stream T (r + k)) -> thunk (k' + k' + k') (Stream T (S r + k')). intros; assert (Stream T (r + S k') = Stream T (S (r + k'))); crush. Qed.

Lemma snoc2 : forall T r k k', k = (S k') -> thunk 11 (BankerQ T (S r + k' + S r)) ->thunk 11 (BankerQ T (S (r + S k' + r))). intros; assert ((BankerQ T (S r + k' + S r)) = (BankerQ T (S (r + S k' + r)))); f_equal; crush. Qed.

Program Definition bq_snoc (T : Type) (a : T) (n : nat) (q : BankerQ T n)
  : thunk 16 (BankerQ T (S n)) :=
  match q with
    | bq k r fs rs => 
      match k with
        |(S k') => ./ ((pay 3 fs) >>= (fun x => ./(snoc2 (k:=k) _ (makebq k' (S r) (snoc1 r _ x) (SCons a (returnw 0 rs))))))
        | 0 => returnw 15 (dummy T (S n))
      end
    | dummy n => returnw 15 (dummy T (S n))
  end.


  

(*
Definition bq_head (T : Type) (n : nat) (default : T) (q : BankerQ T n) : thunk 1 T :=
  match q with
    | bq k r fs rs => fs >>= (fun x => 
      match x with
        | SNil => returnw 0 default
        | SCons _ m _ => returnw 0 m
      end)
    | _ => returnw 0 default
  end.
*)
Lemma ge_minus_one : forall n m : nat, (S n) >= (S m) -> n >= m. crush. Qed.
Check SCons.


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