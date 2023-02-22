(* A tactic for solving equations over boolean groups (where every element has order 2).
This works by reifying expressions and computing a canonical form where an expression is normalized to a bitvector representing whether a particular variable is present in the final expression.
 *)
Require Import Vector.
Import VectorNotations.
Require Import Bool.Bvector.
Require Import Arith.Compare_dec.
Require Import Program.Equality.

Module Type BooleanGroup.
  Parameter A : Set.
  Parameter e : A.
  Parameter f : A -> A -> A.

  Infix "+" := f.

  Axiom assoc : forall a b c, (a + b) + c = a + (b + c).
  Axiom identl : forall a, e + a = a.
  Axiom identr : forall a, a + e = a.
  Axiom order2 : forall a, a + a = e.

End BooleanGroup.


Module BooleanSolver (G : BooleanGroup).
Import G.

  #[local] Hint Rewrite identl identr order2 : algebra.

  (* Commutativity is not postulated as it follows from the other axioms.
    Ironically, this exactly requires the kind of tedious manipulation we are aiming to avoid with this tactic!
    But there's no getting around it, unfortunately. *)
  Theorem comm : forall a b, a + b = b + a.
  Proof.
    intros.
    cut (a = b + a + b).
    intros H.
    apply (f_equal (fun x => x + b)) in H.
    rewrite assoc in H.
    autorewrite with algebra in H.
    assumption.
    cut (e = b + a + b + a).
    intros H.
    apply (f_equal (fun x => x + a)) in H.
    rewrite assoc in H;
    autorewrite with algebra in H.
    assumption.
    replace (b + a + b + a) with ((b + a) + (b + a)).
    autorewrite with algebra.
    reflexivity.
    rewrite <- assoc.
    reflexivity.
  Qed.

Inductive exp (n : nat) : Set :=
| Ident : exp n
| Var : Fin.t n -> exp n
| Op : exp n -> exp n -> exp n.

(* Why are expressions parameterized by n?
   Because we normalize them into a bitvector of finite length, and we need a guarantee that
   our indices aren't too large.
   We could use some other representation (subset types) other than Fin.t, but I don't think there is much benefit from doing so.
   Alternatively, instead of bitvectors, we could use some other representation (e.g., a list of indices representing which indices are currently present).
   But the tradeoff here is that working with this representation (adding) is more cumbersome, while it is very natural to work on bitvectors. *)

Fixpoint mdenote {n : nat} (env: nat -> A) (me : exp n) : A :=
  match me with
    | Ident _ => e
    | Var _ i => env (proj1_sig (Fin.to_nat i))
    | Op _ me1 me2 => mdenote env me1 + mdenote env me2
  end.

Fixpoint denote {n : nat} (env : nat -> A) (v : Bvector n) : A :=
  match v with
    | nil _ => e
    | cons _ x i xs => let y := if x then (env i) else e in
                                 y + denote env xs
  end.

Fixpoint ones (n i : nat) : Bvector n :=
  match n with
    | 0 => Bnil
    | S n' => if (Nat.eqb n' i) then Bcons true n' (Bvect_false n')
              else Bcons false n' (ones n' i)
  end.

(* Define addition on bitvectors using the "convoy" pattern. *)
Fixpoint add {n : nat} (av: Bvector n) : Bvector n -> Bvector n :=
  match av in Vector.t _ n return Vector.t _ n -> Vector.t _ n with
    | [] => fun _ => []
    | ha :: ta => fun b => (xorb ha (Vector.hd b)) :: add ta (Vector.tl b)
  end.
Compute (add (ones 3 2) (ones 3 1)).

Fixpoint normalize {n : nat} (me : exp n) : Bvector n :=
  match me with
    | Ident _ => Bvect_false n
    | Var _ i => ones n (proj1_sig (Fin.to_nat i))
    | Op _ me1 me2 => add (normalize me1) (normalize me2)
  end.

(* Now we are ready to state the main soundness result.
   We prepare by proving some lemmas relating denoting certain forms of expressions and their respective normal forms. *)
Lemma denote_e:
  forall (n : nat) (env : nat -> A), e = denote env (Bvect_false n).
Proof.
  intros n env.
  induction n as [ | ? IHn ]; simpl; [
      reflexivity |
        rewrite <- IHn; autorewrite with algebra; reflexivity ].
Qed.

Lemma eqb_reflect : forall (x y : nat), reflect (x = y) (Nat.eqb x y).
Proof.
  intros x y. apply iff_reflect. symmetry.
  apply PeanoNat.Nat.eqb_eq.
Qed.
#[local] Hint Resolve eqb_reflect : bdestruct.
Ltac bdestruct X :=
  let H := fresh in let e := fresh "e" in
   evar (e: Prop);
   assert (H: reflect e X); subst e;
    [ auto with bdestruct
    | destruct H as [H|H];
       [ | try first [apply not_lt in H | apply not_le in H]]].

(* I couldn't find this exact proof elsewhere, and I didn't want to use a hammer like lia... *)
Lemma sn_not_leq_n : forall n, S n <= n -> False.
Proof.
  induction n; inversion 1; intuition.
Qed.

Lemma denote_var:
  forall (n : nat) (env : nat -> A) (i : nat),
  i < n ->
  env i = denote env (ones n i).
Proof.
  intros n env.
  induction n as [ | ? IHn ]; intros i P.
  - inversion P.
  - inversion P.
    simpl.
    bdestruct (Nat.eqb n n).
    simpl; rewrite <- denote_e; autorewrite with algebra; reflexivity.
    exfalso; apply H; reflexivity.

    simpl.
    bdestruct (Nat.eqb n i).
    rewrite H1 in H0; exfalso; apply (sn_not_leq_n i); assumption.
    simpl; autorewrite with algebra; auto.
Qed.

(* We use dependent destruction so that when we destruct a vector we only consider the valid case
(i.e., a vector of length 0 can only be nil, and a vector of length (S n) can only be cons). *)
Lemma denote_add:
  forall (n : nat) (env : nat -> A) (v1 v2 : Bvector n),
  denote env v1 + denote env v2 =
    denote env (add v1 v2).
Proof.
  intros n env.
  induction v1; intros.
  dependent destruction v2.
  simpl; autorewrite with algebra; reflexivity.

  dependent destruction v2.
  simpl.
  remember (if h then env n else e) as A.
  remember (if h0 then env n else e) as B.
  cut (A + denote env v1 + (B + denote env v2) = (A + B) + (denote env v1 + denote env v2)).
  intros H.
  rewrite H.
  rewrite IHv1.
  apply (f_equal (fun x => x + _)).
  (* Check all four cases. *)
  destruct h, h0; rewrite HeqA, HeqB; simpl; autorewrite with algebra; reflexivity.

  rewrite (assoc A (denote env v1) (B + denote env v2)).
  rewrite <- (assoc (denote env v1) B (denote env v2)).
  rewrite (comm (denote env v1) B).
  rewrite (assoc B (denote env v1) (denote env v2)).
  rewrite <- (assoc A B (denote env v1 + denote env v2)).
  reflexivity.
Qed.

Theorem soundness {n : nat} (env : nat -> A) : forall (me : exp n), mdenote env me = denote env (normalize me).
Proof.
  Local Hint Immediate denote_e denote_var denote_add : core.
  induction me; simpl;
    [ | match goal with | [ t: Fin.t n |- _ ] => destruct (Fin.to_nat t) end
      | repeat (match goal with
                | [ H : mdenote env ?e = denote env (normalize ?e) |- _ ] => rewrite H
                end) ];
    auto.
Qed.

Theorem reflect {n : nat} (env : nat -> A) : forall (me1 me2 : exp n),
  denote env (normalize me1) = denote env (normalize me2) ->
  mdenote env me1 = mdenote env me2.
Proof.
  intros.
  repeat rewrite soundness.
  assumption.
Qed.

(*
To reify: First make a list and collect all variables that appear on both sides of the equality (append to current one if need).
Then walk through expression, replacing each expression that is not e with its lookup from the list.
If we can't find an expression (which shouldn't happen), fail.
 *)

Ltac add_to_list l x :=
  match l with
    | tt => constr:((x, tt))
    | (x, ?xs) => constr:((x, xs))
    | (?x', ?xs) => let xs' := add_to_list xs x in
                     constr:((x', xs'))
  end.

Ltac get_vars env exp :=
  match exp with
    | e => env
    | ?e1 + ?e2 => let env' := get_vars env e1 in
                     get_vars env' e2
    | ?x => add_to_list env x
  end.

Ltac env_length env :=
  match env with
    | tt => constr:(O)
    | (_, ?env') => let l := env_length env' in
                     constr:(S l)
  end.

Ltac lookup env len x :=
  match env with
    | tt => fail "Lookup failed"
    | (x, ?xs) =>
      match len with
        | S ?len' => constr:(@Fin.F1 len')
      end
    | (_, ?xs) =>
      match len with
        | S ?len' =>
          let i := lookup xs len' x in
                    constr:(Fin.FS i)
      end
  end.

Ltac reify env len exp :=
  match exp with
    | e => constr:(Ident len)
    | ?me1 + ?me2 =>
      let r1 := reify env len me1 in
        let r2 := reify env len me2 in
          constr:(Op _ r1 r2)
    | _ => let idx := lookup env len exp in
             constr:(Var _ idx)
  end.

Ltac make_ctx env :=
  match env with
    | tt => constr:(fun (x : nat) => e)
    | (?x, ?xs) => let fn' := make_ctx xs in
                     constr:(fun (n : nat) =>
                               match n with
                                 | O => x
                                 | S n' => fn' n'
                               end)
  end.

Ltac boolgroup :=
  match goal with
    | [ |- ?e1 = ?e2 ] =>
      let env := get_vars tt (e1 + e2) in
        let ctx := make_ctx env in
          let len := env_length env in
            let me1 := reify env len e1 in
              let me2 := reify env len e2 in
                change (mdenote ctx me1 = mdenote ctx me2); apply reflect; reflexivity
  end.

Ltac boolgroup_rw g id :=
  let H := fresh "Hxor" in
  let G := fresh "Hid" in
    assert (H : g = f); auto;
     assert (G : id = e); auto;
     repeat (rewrite H); repeat (rewrite G); boolgroup.


Lemma test : forall (a b c : A) (g : A -> A), a + b + (g a) + c + (g (g b)) + b + c = (g a) + (c + (c + c) + c) + a + g (g b).
  intros ? ? ? g.
  boolgroup.
Qed.

Print test.
Check reflect.

Lemma test1 : forall a b, a + b + b + a = e.
  intros.
  boolgroup.
Qed.

Lemma test2 : forall (a b c : A), c + b + a + a + b + c = e.
  intros; boolgroup.
Qed.

Lemma test2' : forall (a b c : A), c + b + a + a + b + c = e.
  intros.
  rewrite (assoc c b a).
  rewrite (assoc c (b + a) a).
  rewrite (assoc b a a).
  autorewrite with algebra.
  rewrite (assoc c b b).
  autorewrite with algebra.
  reflexivity.
Qed.

Print test2.
Print test2'.

Print test1.

Theorem comm' : forall a b, a + b = b + a.
  intros; boolgroup.
Qed.

End BooleanSolver.

Require Import Coq.NArith.BinNat.
Module XorGroup <: BooleanGroup.
  Definition A := N.
  Definition e := 0%N.
  Definition f := N.lxor.

  Definition assoc := N.lxor_assoc.
  Definition identl := N.lxor_0_l.
  Definition identr := N.lxor_0_r.
  Definition order2 := N.lxor_nilpotent.
End XorGroup.

Module XorSolver := BooleanSolver XorGroup.
Print XorSolver.

Check XorSolver.reflect.

(* Instead of using a module, how about just making the tactics pass around *)
(* the group we are interested in. *)
Infix "**" := XorGroup.f (at level 50).
Lemma xor_lemma : forall (a b c : N), a ** b ** c ** a = (c ** a ** a ** (a ** b)) ** a.
  intros.
  XorSolver.boolgroup.
Qed.

Lemma xor_lemma' : forall (a b c : N), N.lxor a b = N.lxor b a.
  intros.
  XorSolver.boolgroup_rw N.lxor 0%N.
Qed.

Print xor_lemma.

Check nat_of_N.


Search "lxor".
Check N.lxor_comm.

Check N.testbit.
Check N.lxor_spec.

Check N.lxor.
Goal forall x, N.lxor x x = 0%N.
  apply N.lxor_nilpotent.
Qed.

Goal forall x y z, N.lxor (N.lxor x y) z = N.lxor x (N.lxor y z).
  intros. auto.

  Search N.lxor.
  apply N.lxor_assoc.

Qed.

Search N.lxor.

Compute (N.lxor (N.lxor 1%N 2%N) 3%N).
