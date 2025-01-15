Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Require Import core unscoped hopl translation.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.

Notation lup := nth_error.



(* Monotonicity *)

Lemma HOPL_AE' A t phi phi' e :
  HOPL_prv A (tmall t phi) -> phi' = (subst_spec var_type (e..) var_exp) phi -> HOPL_prv A phi'.
Proof.
  intros H ->. now apply HOPL_EAE with t.
Qed.

Lemma int_mono t phi psi m :
  HOPL_prv (tmall t (spimplies phi psi) :: nil) (spimplies (after m phi) (after m psi)).
Proof.
  apply HOPL_II. eapply HOPL_MM. 2: apply HOPL_CTX; now left.
  eapply HOPL_IE. 2: apply HOPL_CTX; now left.
  eapply (HOPL_AE' (e := var_prog 0)).
  - cbn. apply HOPL_CTX. right. right. now left.
  - asimpl. unfold funcomp. f_equal.
    + rewrite idSubst_spec; trivial. now intros [].
    + rewrite idSubst_spec; trivial. now intros [].
Qed.



(* Existential *)

Definition exis s phi :=
  all 1 (implies (all s (implies (ren_form swap phi) (holds (var_term 1) (var_term 2)))) ((holds (var_term 0) (var_term 1)))).

Lemma ip_exis Xi phi s :
  lup Xi 0 = Some 0 -> is_prop (s :: Xi) phi -> is_prop Xi (exis s phi).
Proof.
  intros H1 H2.
  unfold exis.
  apply ip_all, ip_implies.
  - apply ip_all, ip_implies.
    + eapply is_prop_ren; eauto. now intros [].
    + apply ip_holds with 0; now apply hs_var.
  - apply ip_holds with 0; now apply hs_var.
Qed.

Lemma HOL_AE' A s phi phi' p :
  HOL_prv A (all s phi) -> phi' = phi[p..] -> HOL_prv A phi'.
Proof.
  intros H ->. now apply HOL_AE with s.
Qed.

Lemma HOL_CE' A p s phi phi' :
  HOL_prv A (holds (cterm s phi) p) -> phi' = phi[p..] -> HOL_prv A phi'.  
Proof.
  intros H ->. now apply HOL_CE with s.
Qed.

Lemma HOL_eq A phi B psi :
  HOL_prv A phi -> A = B -> phi = psi -> HOL_prv B psi.
Proof.
  intros H -> ->. apply H.
Qed.

Lemma HOL_ren A phi xi :
  HOL_prv A phi -> HOL_prv (map (ren_form xi) A) (ren_form xi phi).
Proof.
  induction 1 in xi |- * ; cbn in *.
  - constructor. now apply in_map.
  - econstructor 2. eauto.
  - econstructor 3; eauto.
  - econstructor 4. eapply HOL_eq. 3: reflexivity.
    + apply IHHOL_prv.
    + rewrite !map_map. apply map_ext. intros psi. now asimpl.
  - eapply HOL_eq. 2: reflexivity.
    + econstructor 5 with (p := p⟨xi⟩). apply IHHOL_prv.
    + cbn. now asimpl.
  - econstructor 6. eapply HOL_eq. 2: reflexivity.
    + apply IHHOL_prv.
    + now asimpl.
  - eapply HOL_eq. 2: reflexivity.
    + econstructor 7. apply IHHOL_prv.
    + now asimpl.
Qed.

Lemma HOL_EI A phi s p :
  HOL_prv A phi[p..] -> HOL_prv A (exis s phi).
Proof.
  intros H. unfold exis. apply HOL_AI, HOL_II.
  apply HOL_IE with (ren_form ↑ (phi[p..])).
  - eapply (HOL_AE' (p := ren_term ↑ p)).
    + apply HOL_CTX. now left.
    + now asimpl.
  - eapply HOL_weak; try apply HOL_ren; eauto. firstorder.
Qed.

Lemma HOL_EE A phi psi s :
  HOL_prv A (exis s phi) -> HOL_prv (phi :: map (ren_form ↑) A) (ren_form ↑ psi) -> HOL_prv A psi.
Proof.
  intros H1 H2. unfold exis in H1. apply (HOL_AE (cterm 42 (ren_form swap psi))) in H1.
  cbn in H1. eapply HOL_CE'.
  - eapply HOL_IE. 1: try apply H1.
    apply HOL_AI. asimpl. rewrite idSubst_form; try now intros [].
    apply HOL_II. apply HOL_CI. asimpl. rewrite rinstInst'_form in H2.
    erewrite ext_form; try apply H2. now intros [].
  - unfold swap. asimpl. rewrite idSubst_form; trivial. now intros [].
Qed.



(* Countable Choice *)

Definition CC s phi : form :=
  all s phi.