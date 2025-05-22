(** * Translation from EffHOL to HOL **)

Set Implicit Arguments.
Unset Strict Implicit.

From Coq.Relations Require Import Relation_Operators.

Require Import List.
Require Import core unscoped syntax HOL EffHOL.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.



(** ** Translation functions **)

Fixpoint trans_sort (o : index) : sort :=
  match o with
  | refb t => 0
  | ref t o => S (trans_sort o)
  | univ k o => (trans_sort o)
  end.

Fixpoint trans_form (phi : spec) : form :=
  match phi with
  | spholds q q' e => holds (trans_term q) (trans_term q')
  | spimplies phi psi => implies (trans_form phi) (trans_form psi)
  | after e phi => trans_form phi
  | tyall k phi => trans_form phi
  | tmall t phi => trans_form phi
  | spall o phi => all (trans_sort o) (trans_form phi)
  end
with trans_term (q : exp) : term :=
  match q with
  | var_exp x => var_term x
  | cexp t o phi => cterm (trans_sort o) (trans_form phi)
  | exabs k q => trans_term q
  | exapp q t => trans_term q
end.

(** ** Simple lemmas **)

Lemma trans_sort_ren o xi :
  trans_sort o⟨xi⟩ = trans_sort o.
Proof.
  induction o in xi |- *; cbn; congruence.
Qed.

Lemma trans_sort_subst o sigma :
  trans_sort o[sigma] = trans_sort o.
Proof.
  induction o in sigma |- *; cbn; trivial. now rewrite IHo.
Qed.

Lemma trans_sort_conv o1 o2 :
  conv_index o1 o2 -> trans_sort o1 = trans_sort o2.
Proof.
  induction 1; cbn; congruence.
Qed.

Lemma trans_form_is_prop Delta Gamma Sigma phi :
  is_spec Delta Gamma Sigma phi -> is_prop (map trans_sort Sigma) (trans_form phi)
with trans_term_has_sort Delta Gamma Sigma q o :
  has_index Delta Gamma Sigma q o -> has_sort (map trans_sort Sigma) (trans_term q) (trans_sort o).
Proof.
  induction 1; cbn.
  - apply ip_implies; assumption.
  - assumption.
  - erewrite map_map, map_ext in IHis_spec; try apply IHis_spec.
    intros. apply trans_sort_ren.
  - assumption.
  - apply ip_all. assumption.
  - eapply ip_holds.
    + apply trans_term_has_sort in H0. apply H0.
    + apply trans_term_has_sort in H1. apply H1.
  - induction 1; cbn.
    + apply hs_var. now apply map_nth_error.
    + apply hs_cterm. apply trans_form_is_prop in H. apply H.
    + erewrite map_map, map_ext in IHhas_index; try apply IHhas_index.
      intros. apply trans_sort_ren.
    + rewrite trans_sort_subst. apply IHhas_index.
    + apply trans_sort_conv in H as <-. apply IHhas_index.
Qed.

Lemma trans_form_ren phi xi1 xi2 xi3 :
  trans_form (ren_spec xi1 xi2 xi3 phi) = (trans_form phi)⟨xi3⟩
with trans_term_ren q xi1 xi2 xi3 :
  trans_term (ren_exp xi1 xi2 xi3 q) = (trans_term q)⟨xi3⟩.
Proof.
  induction phi in xi1, xi2, xi3 |- *.
  - cbn; fold ren_term. now rewrite !trans_term_ren.
  - cbn. now rewrite !trans_form_ren.
  - cbn. now rewrite trans_form_ren.
  - cbn. now rewrite trans_form_ren.
  - cbn. now rewrite trans_form_ren.
  - cbn. now rewrite trans_form_ren, trans_sort_ren.
  - induction q in xi1, xi2, xi3 |- *.
    + reflexivity.
    + cbn; fold ren_form. now rewrite trans_form_ren, trans_sort_ren.
    + cbn. now rewrite trans_term_ren.
    + cbn. now rewrite trans_term_ren.
Qed.

Lemma trans_term_ren' q xi1 xi2 :
  trans_term (ren_exp xi1 xi2 id q) = (trans_term q).
Proof.
  rewrite trans_term_ren. rewrite rinstInst'_term. apply idSubst_term. reflexivity.
Qed.

Lemma trans_form_ren' phi xi1 xi2 :
  trans_form (ren_spec xi1 xi2 id phi) = (trans_form phi).
Proof.
  rewrite trans_form_ren. rewrite rinstInst'_form. apply idSubst_form. reflexivity.
Qed.

Lemma trans_form_subst phi sigma1 sigma2 sigma3 :
  trans_form (subst_spec sigma1 sigma2 sigma3 phi) = (trans_form phi)[sigma3 >> trans_term]
with trans_term_subst q sigma1 sigma2 sigma3 :
  trans_term (subst_exp sigma1 sigma2 sigma3 q) = (trans_term q)[sigma3 >> trans_term].
Proof.
  induction phi in sigma1, sigma2, sigma3 |- *.
  - cbn; fold subst_term. now rewrite !trans_term_subst.
  - cbn. now rewrite !trans_form_subst.
  - cbn. rewrite trans_form_subst. apply ext_form.
    intros x. asimpl. unfold funcomp. apply trans_term_ren'.
  - cbn. rewrite trans_form_subst. apply ext_form.
    intros x. asimpl. unfold funcomp. apply trans_term_ren'.
  - cbn. rewrite trans_form_subst. apply ext_form.
    intros x. asimpl. unfold funcomp. apply trans_term_ren'.
  - cbn. rewrite trans_form_subst, trans_sort_subst. f_equal. apply ext_form.
    intros []; trivial. asimpl. unfold funcomp. apply trans_term_ren.
  - induction q in sigma1, sigma2, sigma3 |- *.
    + reflexivity.
    + cbn; fold subst_form. rewrite trans_sort_subst, trans_form_subst.
      f_equal. apply ext_form. intros []; cbn; trivial.
      asimpl. unfold funcomp. now rewrite trans_term_ren.
    + cbn. rewrite trans_term_subst. apply ext_term.
      intros x. asimpl. unfold funcomp. apply trans_term_ren'.
    + cbn. now rewrite trans_term_subst.
Qed.

Lemma trans_form_subst' phi sigma1 sigma2 :
  trans_form (subst_spec sigma1 sigma2 var_exp phi) = (trans_form phi).
Proof.
  rewrite trans_form_subst. apply idSubst_form. reflexivity.
Qed.

Lemma trans_term_point (phi : form) q :
  phi[q.. >> trans_term] = phi[(trans_term q)..].
Proof.
  apply ext_form. now intros [].
Qed.

Lemma trans_form_conv phi psi :
  conv_spec phi psi -> trans_form phi = trans_form psi
with trans_term_conv q1 q2 :
  conv_exp q1 q2 -> trans_term q1 = trans_term q2.
Proof.
  induction 1; cbn; try congruence.
  - now apply trans_sort_conv in H as ->.
  - now apply trans_term_conv in H as ->.
  - now apply trans_term_conv in H as ->.
  - induction 1; cbn; try congruence.
    + rewrite H. rewrite trans_term_subst. symmetry. apply idSubst_term. reflexivity.
    + now apply trans_sort_conv in H as ->.
    + now apply trans_form_conv in H as ->.
Qed.

(** ** Main result **)

Lemma HOPL_HOL A phi :
  HOPL_prv A phi -> HOL_prv (map trans_form A) (trans_form phi).
Proof.
  induction 1; cbn in *.
  - apply HOL_CTX. now apply in_map.
  - apply HOL_II. apply IHHOPL_prv.
  - eapply HOL_IE; try apply IHHOPL_prv1. apply IHHOPL_prv2.
  - rewrite map_map in *. erewrite map_ext; try apply IHHOPL_prv.
    intros psi. cbn. now rewrite trans_form_ren'.
  - now rewrite trans_form_subst'.
  - rewrite map_map in *. erewrite map_ext; try apply IHHOPL_prv.
    intros psi. cbn. now rewrite trans_form_ren'.
  - now rewrite trans_form_subst'.
  - apply HOL_AI. rewrite map_map in *. erewrite map_ext; try apply IHHOPL_prv.
    intros psi. cbn. now rewrite trans_form_ren.
  - rewrite trans_form_subst, trans_term_point. eapply HOL_AE. eauto.
  - apply HOL_CI. now rewrite trans_form_subst, trans_term_point in IHHOPL_prv.
  - rewrite trans_form_subst, trans_term_point. now apply HOL_CE in IHHOPL_prv.
  - now rewrite trans_form_subst' in IHHOPL_prv.
  - rewrite trans_form_ren' in IHHOPL_prv. assumption.
  - eapply HOL_IE; try apply IHHOPL_prv2. apply HOL_II.
    erewrite map_map, map_ext in IHHOPL_prv1; try apply IHHOPL_prv1.
    intros phi'. apply trans_form_ren'.
  - now rewrite trans_form_subst in *.
  - now apply trans_form_conv in H as <-.
Qed.

Lemma Consistency fal :
  (* assuming that the translation of fal behaves like falsity *)
  (forall phi, HOL_prv nil (implies (trans_form fal) phi))
  (* and assuming that fal behaves like falsity *)
  -> (forall phi, HOPL_prv nil (spimplies fal phi))
  (* any inconsistency in HOPL would imply an inconcistency in HOL *)
  -> HOPL_prv nil fal -> HOL_prv nil (trans_form fal).
Proof.
  intros _ _ H % HOPL_HOL. assumption.
Qed.

Print Assumptions Consistency.