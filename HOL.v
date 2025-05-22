(** * HOL Specification *)

Set Implicit Arguments.
Unset Strict Implicit.

From Coq.Relations Require Import Relation_Operators.

Require Import List.
Require Import core unscoped syntax.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.



(** ** Typing judgements **)

Notation lup := nth_error.

Definition sort := nat.

Inductive has_sort (Xi : list sort) : term -> sort -> Prop :=
| hs_var p s : lup Xi p = Some s -> has_sort Xi (var_term p) s
| hs_cterm phi s : is_prop (s :: Xi) phi -> has_sort Xi (cterm s phi) (S s)

with is_prop (Xi : list sort) : form -> Prop :=
| ip_implies phi psi : is_prop Xi phi -> is_prop Xi psi -> is_prop Xi (implies phi psi)
| ip_all phi s : is_prop (s :: Xi) phi -> is_prop Xi (all s phi)
| ip_holds p p' s : has_sort Xi p (S s) -> has_sort Xi p' s -> is_prop Xi (holds p p').



(** ** HOL deduction system **)

Inductive HOL_prv (A : list form) : form -> Prop :=
| HOL_CTX phi : In phi A -> HOL_prv A phi
| HOL_II phi psi : HOL_prv (phi :: A) psi -> HOL_prv A (implies phi psi)
| HOL_IE phi psi : HOL_prv A (implies phi psi) -> HOL_prv A phi -> HOL_prv A psi
| HOL_AI phi s : HOL_prv (map (ren_form ↑) A) phi -> HOL_prv A (all s phi)
| HOL_AE phi s p : HOL_prv A (all s phi) -> HOL_prv A phi[p..]
| HOL_CI phi s p : HOL_prv A phi[p..] -> HOL_prv A (holds (cterm s phi) p)
| HOL_CE phi s p : HOL_prv A (holds (cterm s phi) p) -> HOL_prv A phi[p..].

Lemma HOL_weak A A' phi :
  HOL_prv A phi -> incl A A' -> HOL_prv A' phi.
Proof.
  induction 1 in A' |- *; intros HA.
  all: try unshelve (solve [econstructor; auto with datatypes]); try now econstructor.
Qed.



(** ** Typed HOL deduction system **)

Inductive THOL_prv (Xi : list sort) (A : list form) : form -> Prop :=
| THOL_CTX phi : In phi A -> is_prop Xi phi -> THOL_prv Xi A phi
| THOL_II phi psi : THOL_prv Xi (phi :: A) psi -> is_prop Xi phi -> THOL_prv Xi A (implies phi psi)
| THOL_IE phi psi : THOL_prv Xi A (implies phi psi) -> THOL_prv Xi A phi -> THOL_prv Xi A psi
| THOL_AI phi s : THOL_prv (s :: Xi) (map (ren_form ↑) A) phi -> THOL_prv Xi A (all s phi)
| THOL_AE phi s p : THOL_prv Xi A (all s phi) -> has_sort Xi p s -> THOL_prv Xi A phi[p..]
| THOL_CI phi s p : THOL_prv Xi A phi[p..] -> has_sort Xi p s -> THOL_prv Xi A (holds (cterm s phi) p)
| THOL_CE phi s p : THOL_prv Xi A (holds (cterm s phi) p) -> THOL_prv Xi A phi[p..].

Lemma THOL_weak Xi A A' phi :
  THOL_prv Xi A phi -> incl A A' -> THOL_prv Xi A' phi.
Proof.
  induction 1 in A' |- *; intros HA.
  all: try unshelve (solve [econstructor; auto with datatypes]); try now econstructor.
Qed.

Lemma is_prop_ren Xi Xi' phi sigma :
  is_prop Xi phi
  -> (forall n s, lup Xi n = Some s -> lup Xi' (sigma n) = Some s)
  -> is_prop Xi' phi⟨sigma⟩
with has_sort_ren Xi Xi' t s sigma :
  has_sort Xi t s
  -> (forall n s, lup Xi n = Some s -> lup Xi' (sigma n) = Some s)
  -> has_sort Xi' t⟨sigma⟩ s.
Proof.
  induction 1 in Xi', sigma |- *; intros HS; cbn.
  - constructor; eauto.
  - constructor. apply IHis_prop. intros [] s'; cbn; eauto.
  - fold ren_term. apply ip_holds with s.
    + eapply has_sort_ren; eauto.
    + eapply has_sort_ren; eauto.
  - induction 1 in Xi', sigma |- *; intros HS; cbn.
    + apply hs_var. now apply HS.
    + fold ren_form. constructor. eapply is_prop_ren; eauto.
      intros [] s'; cbn; eauto.
Qed.

Lemma is_prop_subst Xi Xi' phi sigma :
  is_prop Xi phi
  -> (forall n s, lup Xi n = Some s -> has_sort Xi' (sigma n) s)
  -> is_prop Xi' phi[sigma]
with has_sort_subst Xi Xi' t s sigma :
  has_sort Xi t s
  -> (forall n s, lup Xi n = Some s -> has_sort Xi' (sigma n) s)
  -> has_sort Xi' t[sigma] s.
Proof.
  induction 1 in Xi', sigma |- *; intros HS; cbn.
  - constructor; eauto.
  - constructor. apply IHis_prop. intros [] s'; cbn.
    + intros [=]; subst. now apply hs_var.
    + intros H'. eapply has_sort_ren; eauto.
  - fold subst_term. apply ip_holds with s.
    + eapply has_sort_subst; eauto.
    + eapply has_sort_subst; eauto.
  - induction 1 in Xi', sigma |- *; intros HS; cbn.
    + now apply HS.
    + fold subst_form. constructor. eapply is_prop_subst; eauto.
      intros [] s'; cbn.
      * intros [=]; subst. now apply hs_var.
      * intros H'. eapply has_sort_ren; eauto.
Qed.

Lemma is_prop_ren' Xi Xi' phi sigma :
  (forall n s, lup Xi n = Some s <-> lup Xi' (sigma n) = Some s)
  -> is_prop Xi phi <-> is_prop Xi' phi⟨sigma⟩
with has_sort_ren' Xi Xi' t s sigma :
  (forall n s, lup Xi n = Some s <-> lup Xi' (sigma n) = Some s)
  -> has_sort Xi t s <-> has_sort Xi' t⟨sigma⟩ s.
Proof.
  induction phi in Xi, Xi', sigma |-*; intros HS; cbn; split; inversion 1; subst.
  - constructor. eapply IHphi1; trivial. eapply IHphi2; trivial.
  - constructor. eapply IHphi1; trivial. eapply IHphi2; trivial.
  - constructor. eapply IHphi; eauto. intros [] s'; cbn; eauto. tauto.
  - constructor. eapply IHphi; eauto. intros [] s'; cbn; eauto. tauto.
  - fold ren_term. apply ip_holds with s.
    + rewrite <- has_sort_ren'; eauto.
    + rewrite <- has_sort_ren'; eauto.
  - fold ren_term. apply ip_holds with s.
    + rewrite has_sort_ren'; eauto.
    + rewrite has_sort_ren'; eauto.
  - induction t in Xi, Xi', sigma |- *; intros HS; cbn; split; inversion 1; subst.
    + apply hs_var. now apply HS.
    + apply hs_var. now apply HS.
    + fold ren_form. constructor. rewrite <- is_prop_ren'; eauto.
      intros [] s'; cbn; eauto. tauto.
    + fold ren_form. constructor. rewrite is_prop_ren'; eauto.
      intros [] s'; cbn; eauto. tauto.
Qed.

Lemma is_prop_subst' Xi Xi' phi sigma :
  (forall n s, lup Xi n = Some s <-> has_sort Xi' (sigma n) s)
  -> is_prop Xi phi <-> is_prop Xi' phi[sigma]
with has_sort_subst' Xi Xi' t s sigma :
  (forall n s, lup Xi n = Some s <-> has_sort Xi' (sigma n) s)
  -> has_sort Xi t s <-> has_sort Xi' t[sigma] s.
Proof.
  induction phi in Xi, Xi', sigma |-*; intros HS; cbn; split; inversion 1; subst.
  - constructor. eapply IHphi1; trivial. eapply IHphi2; trivial.
  - constructor. eapply IHphi1; trivial. eapply IHphi2; trivial.
  - constructor. eapply IHphi; eauto. intros [] s'; cbn; split.
    + intros [=]; subst. now apply hs_var.
    + inversion 1; subst. cbn in *. congruence.
    + unfold funcomp. rewrite <- has_sort_ren'; try now apply HS. reflexivity.
    + unfold funcomp. rewrite <- has_sort_ren'; try now apply HS. reflexivity.
  - constructor. eapply IHphi; eauto. intros [] s'; cbn; split.
    + intros [=]; subst. now apply hs_var.
    + inversion 1; subst. cbn in *. congruence.
    + unfold funcomp. rewrite <- has_sort_ren'; try now apply HS. reflexivity.
    + unfold funcomp. rewrite <- has_sort_ren'; try now apply HS. reflexivity.
  - fold subst_term. econstructor; rewrite <- has_sort_subst'; eauto.
  - fold subst_term in *. econstructor; rewrite -> has_sort_subst'; eauto.
  - induction t in Xi, Xi', sigma |-*; intros HS; cbn; split; inversion 1; subst.
    + now apply HS.
    + apply hs_var. apply HS. rewrite <- H0. now apply hs_var.
    + apply hs_var. apply HS. rewrite <- H0. now constructor.
    + fold subst_form. constructor. rewrite <- is_prop_subst'; eauto.
      intros [] s'; cbn; split.
      * intros [=]; subst. now apply hs_var.
      * inversion 1; subst. cbn in *. congruence.
      * unfold funcomp. rewrite <- has_sort_ren'. apply HS. reflexivity.
      * unfold funcomp. rewrite <- has_sort_ren'. apply HS. reflexivity.
    + fold subst_form in *. constructor. rewrite is_prop_subst'; eauto.
      intros [] s'; cbn; split.
      * intros [=]; subst. now apply hs_var.
      * inversion 1; subst. cbn in *. congruence.
      * unfold funcomp. rewrite <- has_sort_ren'. apply HS. reflexivity.
      * unfold funcomp. rewrite <- has_sort_ren'. apply HS. reflexivity.
Qed.

Lemma has_sort_unique Xi t s s' :
  has_sort Xi t s -> has_sort Xi t s' -> s = s'.
Proof.
  induction 1; cbn; inversion 1; subst; congruence.
Qed.

Lemma THOL_is_prop Xi A phi :
  THOL_prv Xi A phi -> is_prop Xi phi.
Proof.
  induction 1; trivial; try constructor; trivial.
  - now inversion IHTHOL_prv1; subst.
  - inversion IHTHOL_prv; subst.
    eapply is_prop_subst; eauto.
    intros [] s'; cbn; try apply hs_var. now intros [=]; subst.
  - econstructor; eauto. constructor. eapply is_prop_subst'; eauto.
    intros [] s'; cbn; split.
    + now intros [=]; subst.
    + intros H'. f_equal. eapply has_sort_unique; eauto.
    + apply hs_var.
    + now inversion 1; subst.
  - inversion IHTHOL_prv; subst. inversion H2; subst.
    eapply is_prop_subst; eauto.
    intros [] s'; cbn; try apply hs_var. now intros [=]; subst.
Qed.