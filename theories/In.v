From Coq Require Import List.
Export ListNotations.
Require Export Coq.Bool.Bool.

(** Some auxillary definitions for list combinators that use functions that *)
(** use a proof that an element is in the list we are operating on. *)
(** This is particularly useful for writing definitions with well-founded recursion. *)
Fixpoint existsb_In {A} (l : list A) : (forall (x : A), In x l -> bool) -> bool :=
  match l with
  | [] => fun _ => false
  | x :: xs => fun f =>
                 orb (f x (or_introl _ eq_refl)) (existsb_In xs (fun x P => f x (or_intror _ P)))
  end.

Lemma existsb_In_existsb {A : Type} :
  forall (l : list A)
         (f : forall x, In x l -> bool)
         (g : A -> bool)
         (H : forall x P, f x P = g x),
    existsb_In l f = existsb g l.
  induction l; auto.
  intros.
  simpl.
  rewrite H.
  apply f_equal.
  apply IHl; auto.
Qed.

Lemma existsb_false {A : Type}:
  forall (l : list A)
         (f : A -> bool),
    existsb f l = false ->
    (forall x, In x l -> f x = false).
  induction l; intuition.
  inversion H0.
  inversion H0; subst.
  simpl in H. apply orb_false_iff in H. intuition.
  apply IHl; auto.
  simpl in H. apply orb_false_iff in H; intuition.
Qed.

Lemma existsb_In_ext :
  forall A
         (l : list A)
         (f g: forall x, In x l -> bool)
         (EXT : forall x P, f x P = g x P),
    existsb_In l f = existsb_In l g.
  intros.
  induction l as [ | x l IH ]; auto.
  simpl.
  rewrite EXT.
  f_equal.
  apply IH; auto.
Qed.

Fixpoint map_In {A B} (l : list A) : (forall (x : A), In x l -> B) -> list B :=
  match l with
  | [] => fun _ => []
  | x :: xs => fun f =>
                 f x (or_introl _ eq_refl) :: map_In xs (fun x P => f x (or_intror _ P))
  end.

Lemma map_In_map {A B : Type} :
  forall (l : list A)
         (f : forall (x : A), In x l -> B)
         (g : A -> B)
         (H : forall x P, f x P = g x),
    map_In l f = map g l.
Proof.
  induction l; auto.
  intros.
  simpl.
  rewrite H.
  apply f_equal.
  apply IHl; auto.
Qed.

Lemma map_In_ext :
  forall A B
         (l : list A)
         (f g: forall (x : A), In x l -> B)
         (EXT : forall x P, f x P = g x P),
    map_In l f = map_In l g.
Proof.
  intros.
  induction l as [ | x l IH ]; auto.
  simpl.
  rewrite EXT.
  f_equal.
  apply IH; auto.
Qed.
