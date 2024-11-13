Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Require Import core unscoped hopl.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.

Notation lup := nth_error.


(** Reduction and conversion **)

Inductive is_value : prog -> Prop :=
| iv_var x : is_value (var_prog x)
| iv_tyabs k e : is_value (tyabs k e)
| iv_tmapp t e : is_value (tmabs t e)
| iv_ret e : is_value (ret e).

Inductive red_prog : prog -> prog -> Prop :=
| rp_trans e1 e2 e3 : red_prog e1 e2 -> red_prog e2 e3 -> red_prog e1 e3
| rp_betaty k e t t' : t' = subst_prog (t..) var_prog e -> red_prog (tyapp (tyabs k e) t) t'
| rp_betatm t e1 e2 e : e = subst_prog var_type (e2..) e1 -> is_value e2 -> red_prog (tmapp (tmabs t e1) e2) e
| rp_ret e1 e2 e : e = subst_prog var_type (e1..) e2 -> red_prog (bind (ret e1) e2) e
| rp_tyapp e1 e2 t : red_prog e1 e2 -> red_prog (tyapp e1 t) (tyapp e2 t)
| rp_tmapp1 e1 e2 e : red_prog e1 e2 -> red_prog (tmapp e1 e) (tmapp e2 e)
| rp_tmapp2 e1 e2 e : red_prog e1 e2 -> is_value e -> red_prog (tmapp e e1) (tmapp e e2)
| rp_bind e1 e2 e : red_prog e1 e2 -> red_prog (bind e1 e) (bind e2 e).

Inductive conv_type : type -> type -> Prop :=
| ct_refl t : conv_type t t
| ct_sym t1 t2 : conv_type t1 t2 -> conv_type t2 t1
| ct_trans t1 t2 t3 : conv_type t1 t2 -> conv_type t2 t3 -> conv_type t1 t3
| ct_beta k t1 t2 t : t = subst_type (t2..) t1 -> conv_type (app (abs k t1) t2) t
| ct_app1 t1 t2 t : conv_type t1 t2 -> conv_type (app t1 t) (app t2 t)
| ct_app2 t1 t2 t : conv_type t1 t2 -> conv_type (app t t1) (app t t2)
| ct_arrow1 t1 t2 t : conv_type t1 t2 -> conv_type (arrow t1 t) (arrow t2 t)
| ct_arrow2 t1 t2 t : conv_type t1 t2 -> conv_type (arrow t t1) (arrow t t2)
| ct_pi t1 t2 k : conv_type t1 t2 -> conv_type (pi k t1) (pi k t2)
| ct_comp t1 t2 : conv_type t1 t2 -> conv_type (comp t1) (comp t2).

Inductive conv_prog : prog -> prog -> Prop :=
| cp_refl e : conv_prog e e
| cp_sym e1 e2 : conv_prog e1 e2 -> conv_prog e2 e1
| cp_trans e1 e2 e3 : conv_prog e1 e2 -> conv_prog e2 e3 -> conv_prog e1 e3
| cp_tyapp e t1 t2 : conv_type t1 t2 -> conv_prog (tyapp e t1) (tyapp e t2).

Inductive conv_index : index -> index -> Prop :=
| ci_refl o : conv_index o o
| ci_sym o1 o2 : conv_index o1 o2 -> conv_index o2 o1
| ci_trans o1 o2 o3 : conv_index o1 o2 -> conv_index o2 o3 -> conv_index o1 o3
| ci_refb t1 t2 : conv_type t1 t2 -> conv_index (refb t1) (refb t2)
| ci_ref_type t1 t2 o : conv_type t1 t2 -> conv_index (ref t1 o) (ref t2 o)
| ci_ref_index o1 o2 t : conv_index o1 o2 -> conv_index (ref t o1) (ref t o2)
| ci_univ o1 o2 k : conv_index o1 o2 -> conv_index (univ k o1) (univ k o2).

Inductive conv_exp : exp -> exp -> Prop :=
| ce_refl q : conv_exp q q
| ce_sym q1 q2 : conv_exp q1 q2 -> conv_exp q2 q1
| ce_trans q1 q2 q3 : conv_exp q1 q2 -> conv_exp q2 q3 -> conv_exp q2 q3
| ce_beta k q t q' : q' = subst_exp (t..) var_prog var_exp q -> conv_exp (exapp (exabs k q) t) q'
| ce_exabs k q1 q2 : conv_exp q1 q2 -> conv_exp (exabs k q1) (exabs k q2)
| ce_exapp_type t1 t2 q : conv_type t1 t2 -> conv_exp (exapp q t1) (exapp q t2)
| ce_cexp_type t1 t2 q phi : conv_type t1 t2 -> conv_exp (cexp t1 q phi) (cexp t2 q phi)
| ce_cexp_index t q1 q2 phi : conv_index q1 q2 -> conv_exp (cexp t q1 phi) (cexp t q2 phi)
| ce_cexp_spec t q phi psi : conv_spec phi psi -> conv_exp (cexp t q phi) (cexp t q psi)

with conv_spec : spec -> spec -> Prop :=
| cs_refl phi : conv_spec phi phi
| cs_sym phi psi : conv_spec phi psi -> conv_spec psi phi
| cs_trans phi psi theta : conv_spec phi psi -> conv_spec psi theta -> conv_spec phi theta
| cs_implies1 phi1 phi2 psi : conv_spec phi1 phi2 -> conv_spec (spimplies phi1 psi) (spimplies phi2 psi)
| cs_implies2 phi psi1 psi2 : conv_spec psi1 psi2 -> conv_spec (spimplies phi psi1) (spimplies phi psi2)
| cs_after_prog e1 e2 phi : conv_prog e1 e2 -> conv_spec (after e1 phi) (after e2 phi)
| cs_after_spec e phi psi : conv_spec phi psi -> conv_spec (after e phi) (after e psi)
| cs_tyall k phi psi : conv_spec phi psi -> conv_spec (tyall k phi) (tyall k psi)
| cs_tmall_type t1 t2 phi : conv_type t1 t2 -> conv_spec (tmall t1 phi) (tmall t2 phi)
| cs_tmall_spec t phi psi : conv_spec phi psi -> conv_spec (tmall t phi) (tmall t psi)
| cs_spall_index o1 o2 phi : conv_index o1 o2 -> conv_spec (spall o1 phi) (spall o2 phi)
| cs_spall_spec o phi psi : conv_spec phi psi -> conv_spec (spall o phi) (spall o psi)
| cs_holds_prog q1 q2 e1 e2 : conv_prog e1 e2 -> conv_spec (spholds q1 q2 e1) (spholds q1 q2 e2)
| cs_holds_exp1 q1 q1' q2 e : conv_exp q1 q1' -> conv_spec (spholds q1 q2 e) (spholds q1' q2 e)
| cs_holds_exp2 q1 q2 q2' e : conv_exp q2 q2' -> conv_spec (spholds q1 q2 e) (spholds q1 q2' e).



(** Typing judgements **)

Definition sort := nat.
Definition kind := nat.

Inductive has_sort (Xi : list sort) : term -> sort -> Prop :=
| hs_var p s : lup Xi p = Some s -> has_sort Xi (var_term p) s
| hs_cterm phi s : is_prop (s :: Xi) phi -> has_sort Xi (cterm s phi) (S s)

with is_prop (Xi : list sort) : form -> Prop :=
| ip_implies phi psi : is_prop Xi phi -> is_prop Xi psi -> is_prop Xi (implies phi psi)
| ip_all phi s : is_prop (s :: Xi) phi -> is_prop Xi (all s phi)
| ip_holds p p' s : has_sort Xi p (S s) -> has_sort Xi p' s -> is_prop Xi (holds p p').

Inductive has_kind (Delta : list kind) : type -> kind -> Prop :=
| hk_var X k : lup Delta X = Some k
               -> has_kind Delta (var_type X) k
| hk_app t1 t2 k : has_kind Delta t1 (S k)
                   -> has_kind Delta t2 k
                   -> has_kind Delta (app t1 t2) 0
| hk_abs t k : has_kind (k :: Delta) t 0
               -> has_kind Delta (abs k t) (S k)
| hk_arrow t1 t2 : has_kind Delta t1 0
                   -> has_kind Delta t2 0
                   -> has_kind Delta (arrow t1 t2) 0
| hk_pi t k : has_kind (k::Delta) t 0
              -> has_kind Delta (pi k t) 0
| hk_comp t : has_kind Delta t 0
              -> has_kind Delta (comp t) 0.

Inductive has_type (Delta : list kind) (Gamma : list type) : prog -> type -> Prop :=
| ht_var x t : lup Gamma x = Some t
               -> has_type Delta Gamma (var_prog x) t
| ht_tyabs e t k : has_type (k :: Delta) (map (ren_type ↑) Gamma) e t
                   -> has_type Delta Gamma (tyabs k e) (pi k t)
| ht_tmabs e t1 t2 : has_type Delta (t1 :: Gamma) e (comp t2)
                     -> has_type Delta Gamma (tmabs t1 e) (arrow t1 t2)
| ht_ret e t : has_type Delta Gamma e t
               -> has_type Delta Gamma (ret e) (comp t)
| ht_bind e1 e2 t1 t2 : has_type Delta Gamma e1 (comp t1)
                        -> has_type Delta (t1 :: Gamma) e2 (comp t2)
                        -> has_type Delta Gamma (bind e1 e2) (comp t2)
| ht_tyapp e t1 t2 k : has_type Delta Gamma e (pi k t1)
                       -> has_kind Delta t2 k
                       -> has_type Delta Gamma (tyapp e t2) t1[t2..]
| ht_tmapp e1 e2 t1 t2 : has_type Delta Gamma e1 (arrow t1 t2)
                         -> has_type Delta Gamma e2 t1
                         -> has_type Delta Gamma (tmapp e1 e2) (comp t2)
| ht_conv e t1 t2 : conv_type t1 t2
                    -> has_type Delta Gamma e t1
                    -> has_type Delta Gamma e t2.

Inductive is_index (Delta : list kind) : index -> Prop :=
| ii_refb t : has_kind Delta t 0 -> is_index Delta (refb t)
| ii_ref o t : has_kind Delta t 0 -> is_index Delta o -> is_index Delta (ref t o)
| ii_univ o k : is_index (k :: Delta) o -> is_index Delta (univ k o).

Inductive has_index (Delta : list kind) (Gamma : list type) (Sigma : list index) : exp -> index -> Prop :=
| hi_var q o : lup Sigma q = Some o
               -> has_index Delta Gamma Sigma (var_exp q) o
| hi_cexp phi t o : is_spec Delta (t :: Gamma) (o :: Sigma) phi
                  -> has_index Delta Gamma Sigma (cexp t o phi) (ref t o)
| hi_exabs q k o : has_index (k :: Delta) (map (ren_type ↑) Gamma) (map (ren_index ↑) Sigma) q o
                   -> has_index Delta Gamma Sigma (exabs k q) (univ k o)
| hi_exapp q k t o : has_index Delta Gamma Sigma q (univ k o)
                     -> has_kind Delta t k
                     -> has_index Delta Gamma Sigma (exapp q t) o[t..]
| hi_conv e o1 o2 : conv_index o1 o2
                    -> has_index Delta Gamma Sigma e o1
                    -> has_index Delta Gamma Sigma e o2

with is_spec (Delta : list kind) (Gamma : list type) (Sigma : list index) : spec -> Prop :=
| is_implies phi psi : is_spec Delta Gamma Sigma phi
                   -> is_spec Delta Gamma Sigma psi
                   -> is_spec Delta Gamma Sigma (spimplies phi psi)
| is_after phi e t : is_spec Delta (t :: Gamma) Sigma phi
                   -> has_type Delta Gamma e (comp t)
                   -> is_spec Delta Gamma Sigma (after e phi)
| is_tyall phi k : is_spec (k :: Delta) (map (ren_type ↑) Gamma) (map (ren_index ↑) Sigma) phi
                 -> is_spec Delta Gamma Sigma (tyall k phi)
| is_tmall phi t : is_spec Delta (t :: Gamma) Sigma phi
                   -> is_spec Delta Gamma Sigma (tmall t phi)
| is_spall phi o : is_spec Delta Gamma (o :: Sigma) phi
                 -> is_index Delta o
                 -> is_spec Delta Gamma Sigma (spall o phi)
| is_holds e t q q' o : has_type Delta Gamma e t
                        -> has_index Delta Gamma Sigma q (ref t o)
                        -> has_index Delta Gamma Sigma q' o
                        -> is_spec Delta Gamma Sigma (spholds q q' e).



(** HOL deduction system **)

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



(** HOPL deduction system **)

Inductive HOPL_prv (A : list spec) : spec -> Prop :=
| HOPL_CTX phi : In phi A
               -> HOPL_prv A phi
| HOPL_II phi psi : HOPL_prv (phi :: A) psi
                -> HOPL_prv A (spimplies phi psi)
| HOPL_IE phi psi : HOPL_prv A (spimplies phi psi)
                -> HOPL_prv A phi
                -> HOPL_prv A psi
| HOPL_TAI phi k : HOPL_prv (map (ren_spec ↑ id id) A) phi
                 -> HOPL_prv A (tyall k phi)
| HOPL_TAE phi k t : HOPL_prv A (tyall k phi)
                   -> HOPL_prv A (subst_spec (t..) var_prog var_exp phi)
| HOPL_EAI phi t : HOPL_prv (map (ren_spec id ↑ id) A) phi
                 -> HOPL_prv A (tmall t phi)
| HOPL_EAE phi e t : HOPL_prv A (tmall t phi)
                   -> HOPL_prv A (subst_spec var_type (e..) var_exp phi)
| HOPL_SAI phi o : HOPL_prv (map (ren_spec id id ↑) A) phi
                 -> HOPL_prv A (spall o phi)
| HOPL_SAE phi o q : HOPL_prv A (spall o phi)
                   -> HOPL_prv A (subst_spec var_type var_prog (q..) phi)
| HOPL_CI phi t o e q : HOPL_prv A (subst_spec var_type (e..) (q..) phi)
                      -> HOPL_prv A (spholds (cexp t o phi) q e)
| HOPL_CE phi t o e q : HOPL_prv A (spholds (cexp t o phi) q e)
                      -> HOPL_prv A (subst_spec var_type (e..) (q..) phi)
| HOPL_MI phi e : HOPL_prv A (subst_spec var_type (e..) var_exp phi)
                -> HOPL_prv A (after (ret e) phi)
| HOPL_ME phi e1 e2 : HOPL_prv A (after e1 (after e2 (ren_spec id ↑ id phi)))
                    -> HOPL_prv A (after (bind e1 e2) phi)
| HOPL_MM phi psi e : HOPL_prv (phi :: map (ren_spec id ↑ id) A) psi
                  -> HOPL_prv A (after e phi)
                  -> HOPL_prv A (after e psi)
| HOPL_RED phi e1 e2 : red_prog e1 e2
                    -> HOPL_prv A (subst_spec var_type (e2..) var_exp phi)
                    -> HOPL_prv A (subst_spec var_type (e1..) var_exp phi)
| HOPL_CONV phi psi : conv_spec phi psi
                  -> HOPL_prv A phi
                  -> HOPL_prv A psi.

Lemma HOPL_weak A A' phi :
  HOPL_prv A phi -> incl A A' -> HOPL_prv A' phi.
Proof.
  induction 1 in A' |- *; intros HA.
  all: try unshelve (solve [econstructor; auto with datatypes]); try now econstructor.
  - eapply HOPL_RED; eauto.
  - eapply HOPL_CONV; eauto.
Qed.

Lemma HOPL_eq A phi B psi :
  HOPL_prv A phi -> A = B -> phi = psi -> HOPL_prv B psi.
Proof.
  intros H -> ->. apply H.
Qed.



(** Translation from HOPL to HOL **)

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



(** Judgement weakening lemmas **)

Lemma has_kind_weak Delta Delta' t k :
  has_kind Delta t k -> has_kind (Delta ++ Delta') t k.
Proof.
  induction 1; econstructor; intuition; eauto.
  rewrite nth_error_app1; trivial. apply nth_error_Some. congruence.
Qed.



(** Judgement renaming lemmas **)

Lemma has_kind_ren Delta Delta' t k xi :
  has_kind Delta t k
  -> (forall x k', lup Delta x = Some k' -> lup Delta' (xi x) = Some k')
  -> has_kind Delta' t⟨xi⟩ k.
Proof.
  induction 1 in Delta', xi |- *; cbn; intros HD.
  - apply hk_var. now apply HD.
  - apply hk_app with k; intuition.
  - apply hk_abs. apply IHhas_kind. intros []; firstorder.
  - apply hk_arrow; intuition.
  - apply hk_pi. apply IHhas_kind. intros []; firstorder.
  - apply hk_comp. now apply IHhas_kind.
Qed.

Lemma conv_type_ren t1 t2 xi :
  conv_type t1 t2 -> conv_type t1⟨xi⟩ t2⟨xi⟩.
Proof.
  induction 1 in xi |-*; cbn.
  - apply ct_refl.
  - now apply ct_sym.
  - eapply ct_trans; eauto.
  - apply ct_beta. rewrite H. now asimpl.
  - now apply ct_app1.
  - now apply ct_app2.
  - now apply ct_arrow1.
  - now apply ct_arrow2.
  - now apply ct_pi.
  - now apply ct_comp.
Qed.

Lemma has_type_ren Delta Delta' Gamma Gamma' xi rho e t :
  has_type Delta Gamma e t
  -> (forall n k, lup Delta n = Some k -> lup Delta' (xi n) = Some k)
  -> (forall n t', lup Gamma n = Some t' -> lup Gamma' (rho n) = Some (ren_type xi t'))
  -> has_type Delta' Gamma' (ren_prog xi rho e) (ren_type xi t).
Proof.
  induction 1 in xi, rho, Delta', Gamma' |- *; intros HD HG; cbn.
  - apply ht_var. now apply HG.
  - apply ht_tyabs. apply IHhas_type.
    + intros []; cbn; intuition.
    + intros n0 t' H0. rewrite nth_error_map in H0.
      destruct (lup Gamma n0) eqn: He; cbn in *; try discriminate.
      injection H0 as []. erewrite renRen_type, extRen_type, <- renRen_type.
      * apply map_nth_error. now apply HG.
      * now intros [].
  - apply ht_tmabs. apply IHhas_type.
    + intros []; cbn; intuition.
    + intros []; cbn; intros; try now injection H0 as ->. now apply HG.
  - apply ht_ret. apply IHhas_type; eauto.
  - apply ht_bind with t1⟨xi⟩.
    + apply IHhas_type1; eauto.
    + apply IHhas_type2; eauto. intros []; cbn; intuition.
      unfold upRen_prog_type. now injection H1 as ->.
  - cbn. asimpl. erewrite ext_type, <- renSubst_type at 1.
    + apply ht_tyapp with k.
      * apply IHhas_type; eauto.
      * eapply has_kind_ren; try apply H0. apply HD.
    + now intros [].
  - apply ht_tmapp with t1⟨xi⟩.
    + apply IHhas_type1; eauto.
    + apply IHhas_type2; eauto.
  - apply ht_conv with t1⟨xi⟩.
    + now apply conv_type_ren.
    + apply IHhas_type; eauto.
Qed.

Lemma is_index_ren Delta Delta' xi o :
  is_index Delta o
  -> (forall n k, lup Delta n = Some k -> lup Delta' (xi n) = Some k)
  -> is_index Delta' o⟨xi⟩.
Proof.
  induction 1 in Delta', xi |- *; intros HD; cbn.
  - apply ii_refb. now apply (has_kind_ren H).
  - apply ii_ref; try now apply (has_kind_ren H). now apply IHis_index; try apply H3.
  - apply ii_univ. apply IHis_index; try apply H1. intros []; cbn in *; intuition.
Qed.

Lemma conv_index_ren o1 o2 xi :
  conv_index o1 o2 -> conv_index o1⟨xi⟩ o2⟨xi⟩.
Proof.
  induction 1 in xi |-*; cbn.
  - apply ci_refl.
  - now apply ci_sym.
  - eapply ci_trans; eauto.
  - apply ci_refb. now apply conv_type_ren.
  - apply ci_ref_type. now apply conv_type_ren.
  - now apply ci_ref_index.
  - now apply ci_univ.
Qed.

Lemma is_spec_ren Delta Delta' Gamma Gamma' Sigma Sigma' tren pren eren phi :
  is_spec Delta Gamma Sigma phi
  -> (forall n k, lup Delta n = Some k -> lup Delta' (tren n) = Some k)
  -> (forall n t, lup Gamma n = Some t -> lup Gamma' (pren n) = Some (ren_type tren t))
  -> (forall n o, lup Sigma n = Some o -> lup Sigma' (eren n) = Some (ren_index tren o))
  -> is_spec Delta' Gamma' Sigma' (ren_spec tren pren eren phi)
with has_index_ren Delta Delta' Gamma Gamma' Sigma Sigma' tren pren eren q o :
  has_index Delta Gamma Sigma q o
  -> (forall n k, lup Delta n = Some k -> lup Delta' (tren n) = Some k)
  -> (forall n t, lup Gamma n = Some t -> lup Gamma' (pren n) = Some (ren_type tren t))
  -> (forall n o, lup Sigma n = Some o -> lup Sigma' (eren n) = Some (ren_index tren o))
  -> has_index Delta' Gamma' Sigma' (ren_exp tren pren eren q) o⟨tren⟩.
Proof.
  induction 1 in Delta', Gamma', Sigma', tren, pren, eren |- *; intros HD HG HS; cbn.
  - apply is_implies; eauto.
  - apply is_after with t⟨tren⟩.
    + apply IHis_spec; eauto. destruct n; cbn in *; intuition. now injection H1 as ->.
    + eapply has_type_ren in H0; eauto.
  - apply is_tyall. apply IHis_spec; eauto.
    + intros [] k'; cbn; intuition.
    + intros n0 t' H0. rewrite nth_error_map in H0.
      destruct (lup Gamma n0) eqn: He; cbn in *; try discriminate.
      injection H0 as []. erewrite renRen_type, extRen_type, <- renRen_type.
      * apply map_nth_error. now apply HG.
      * now intros [].
    + intros n0 t' H0. rewrite nth_error_map in H0.
      destruct (lup Sigma n0) eqn: He; cbn in *; try discriminate.
      injection H0 as []. erewrite renRen_index, extRen_index, <- renRen_index.
      * apply map_nth_error. now apply HS.
      * now intros [].
  - apply is_tmall. apply IHis_spec; eauto.
    intros [] t0; cbn; try apply HG.
    intros [=]; subst. reflexivity.
  - apply is_spall; try eapply is_index_ren; eauto. apply IHis_spec; try apply H2; intuition.
    destruct n; cbn in *; intuition. now injection H1 as ->.
  - eapply is_holds.
    + eapply has_type_ren; try apply H; intuition.
    + eapply has_index_ren in H0; eauto.
    + fold ren_index. eapply has_index_ren in H1; eauto.
  - induction 1 in Delta', Gamma', Sigma', tren, pren, eren |- *; intros HD HG HS; cbn.
    + apply hi_var. now apply HS.
    + apply hi_cexp. eapply is_spec_ren; try apply H; intuition.
      * destruct n; cbn in *; intuition. now injection H0 as ->.
      * destruct n; cbn in *; intuition. now injection H0 as ->.
    + apply hi_exabs. apply IHhas_index; intuition.
      * destruct n; cbn in *; intuition.
      * rewrite nth_error_map in H0.
        destruct (lup Gamma n) eqn: He; cbn in *; try discriminate.
        injection H0 as []. erewrite renRen_type, extRen_type, <- renRen_type.
        -- apply map_nth_error. now apply HG.
        -- now intros [].
      * rewrite nth_error_map in H0.
        destruct (lup Sigma n) eqn: He; cbn in *; try discriminate.
        injection H0 as []. erewrite renRen_index, extRen_index, <- renRen_index.
        -- apply map_nth_error. now apply HS.
        -- now intros [].
    + erewrite compSubstRen_index, ext_index, <- compRenSubst_index. eapply hi_exapp.
      apply IHhas_index; try apply H; intuition. 2,3: reflexivity.
      * eapply has_kind_ren; eauto.
      * now intros [].
    + apply hi_conv with o1⟨tren⟩.
      * now apply conv_index_ren.
      * apply IHhas_index; eauto. 
Qed.

Lemma is_spec_ren' Delta Gamma Gamma' Sigma xi phi :
  is_spec Delta Gamma Sigma phi
  -> (forall n t, lup Gamma n = Some t -> lup Gamma' (xi n) = Some t)
  -> is_spec Delta Gamma' Sigma (ren_spec id xi id phi).
Proof.
  intros H1 H2. eapply is_spec_ren; try apply H1; intuition.
  - rewrite rinstId'_type. intuition.
  - rewrite rinstId'_index. intuition.
Qed.



(** Translation from HOL to HOPL **)

Fixpoint trans_I (s : sort) (t : type) : index :=
  match s with 
  | 0 => refb t
  | S s => univ s (ref (app t⟨↑⟩ (var_type 0)) (trans_I s (var_type 0)))
  end.

Fixpoint trans_T (phi : form) : type :=
  match phi with
  | implies phi psi => arrow (trans_T phi) (trans_T psi)
  | all s phi => pi s (comp (trans_T phi))
  | holds p p' => app (ttrans_T p) (ttrans_T p')
  end
with ttrans_T (p : term) : type :=
  match p with 
  | var_term x => var_type x
  | cterm s phi => abs s (trans_T phi)
  end.

Definition swap := 0 .: (↑ >> ↑).

Fixpoint trans_S (phi : form) (e : prog) : spec :=
  match phi with
  | implies phi psi => tmall (trans_T phi)
                        (spimplies (trans_S phi (var_prog 0))
                                   (after (tmapp (ren_prog id ↑ e) (var_prog 0))
                                          (ren_spec id swap id (trans_S psi (var_prog 0)))))
  | all s phi => tyall s (spall (trans_I s (var_type 0))
                             (after (tyapp (ren_prog ↑ id e) (var_type 0))
                                    (trans_S phi (var_prog 0))))
  | holds p p' => spholds (exapp (ttrans_E p) (ttrans_T p')) (ttrans_E p') e
  end
with ttrans_E (p : term) : exp :=
  match p with
  | var_term x => var_exp x
  | cterm s phi => exabs s (cexp (trans_T phi) (trans_I s (var_type 0)) (trans_S phi (var_prog 0)))
  end.

Fixpoint trans_IL' (SL : list sort) n : list index :=
  match SL with
  | nil => nil
  | s :: SL => trans_I s (var_type n) :: trans_IL' SL (S n)
  end.

Definition trans_IL SL :=
  trans_IL' SL 0.

Fixpoint trans_SL' (Psi : list form) n : list spec :=
  match Psi with
  | nil => nil
  | psi :: Psi => trans_S psi (var_prog n) :: trans_SL' Psi (S n)
  end.

Definition trans_SL Psi :=
  trans_SL' Psi 0.



(** Translation substitution lemmas **)

Lemma trans_I_subst s t sigma :
  (trans_I s t)[sigma] = trans_I s t[sigma].
Proof.
  induction s in t, sigma |- *; cbn; trivial.
  rewrite IHs. now asimpl.
Qed.

Lemma trans_I_ren s t xi :
  (trans_I s t)⟨xi⟩ = trans_I s t⟨xi⟩.
Proof.
  rewrite rinstInst_type, rinstInst_index. apply trans_I_subst.
Qed.

Lemma trans_T_ren phi sigma :
  (trans_T phi)⟨sigma⟩ = trans_T phi⟨sigma⟩
with ttrans_T_ren t sigma :
  (ttrans_T t)⟨sigma⟩ = ttrans_T t⟨sigma⟩.
Proof.
  induction phi in sigma |- *; cbn; fold ren_term.
  - now rewrite IHphi1, IHphi2.
  - now rewrite <- IHphi.
  - now rewrite !ttrans_T_ren.
  - induction t in sigma |- *; cbn; fold ren_form; trivial.
    now rewrite <- trans_T_ren.
Qed.

Lemma trans_T_subst phi sigma :
  (trans_T phi)[sigma >> ttrans_T] = trans_T phi[sigma]
with ttrans_T_subst t sigma :
  (ttrans_T t)[sigma >> ttrans_T] = ttrans_T t[sigma].
Proof.
  induction phi in sigma |- *; cbn; fold subst_term.
  - now rewrite IHphi1, IHphi2.
  - rewrite <- IHphi. f_equal. f_equal. apply ext_type. intros []; cbn; trivial. apply ttrans_T_ren.
  - now rewrite !ttrans_T_subst.
  - induction t in sigma |- *; cbn; fold subst_form; trivial.
    rewrite <- trans_T_subst. f_equal. apply ext_type. intros []; cbn; trivial. apply ttrans_T_ren.
Qed.

(*Lemma trans_S_subst' phi e sigma xi :
  subst_spec (sigma >> ttrans_T) xi (sigma >> ttrans_E) (trans_S phi e)
  = trans_S (subst_form sigma phi) (subst_prog (sigma >> ttrans_T) xi e).
Proof.
  induction phi in e, sigma, xi |- *; cbn.
  - f_equal; try apply trans_T_subst. f_equal. 2: f_equal.
    + change (var_prog 0) with (subst_prog (sigma >> ttrans_T) (up_prog_prog xi) (var_prog 0)) at 2.
      rewrite <- IHphi1. apply ext_spec; try now intros [].
Admitted.*)

Lemma trans_S_ren phi x sigma :
  ren_spec sigma id sigma (trans_S phi (var_prog x)) = trans_S (ren_form sigma phi) (var_prog x)
with ttrans_E_ren t sigma :
  ren_exp sigma id sigma (ttrans_E t) = ttrans_E (ren_term sigma t).
Proof.
  induction phi in x, sigma |- *; cbn.
  - rewrite trans_T_ren. f_equal. f_equal.
    + rewrite <- IHphi1. apply extRen_spec; try reflexivity. now intros [].
    + f_equal. rewrite <- IHphi2. now asimpl.
  - f_equal. f_equal; try apply trans_I_ren. asimpl. unfold funcomp. f_equal.
    rewrite <- IHphi. apply extRen_spec; trivial. now intros [].
  - now rewrite !ttrans_E_ren, ttrans_T_ren.
  - induction t in sigma |- *; cbn; trivial. f_equal. f_equal.
    + now rewrite trans_T_ren.
    + now rewrite trans_I_ren.
    + asimpl. unfold funcomp. rewrite <- trans_S_ren. apply extRen_spec; trivial. now intros [].
Qed.

Lemma trans_S_subst phi x sigma :
  subst_spec (sigma >> ttrans_T) var_prog (sigma >> ttrans_E) (trans_S phi (var_prog x))
  = trans_S (subst_form sigma phi) (var_prog x).
Proof.
  induction phi in x, sigma |- *; cbn.
  - admit.
  - f_equal. f_equal; try apply trans_I_subst. asimpl. unfold funcomp. f_equal.
    rewrite <- IHphi. apply ext_spec; intros []; cbn; trivial.
    + apply ttrans_T_ren.
    + admit.
Admitted.

Lemma trans_S_subst_spec phi e sigma :
  subst_spec var_type sigma var_exp (trans_S phi e) = trans_S phi (subst_prog var_type sigma e)
with ttrans_E_subst_exp t sigma :
  subst_exp var_type sigma var_exp (ttrans_E t) = ttrans_E t.
Proof.
  induction phi in e, sigma |- *; cbn.
  - rewrite instId'_type. f_equal. f_equal. 2: f_equal.
    + asimpl. unfold funcomp. now rewrite IHphi1.
    + now asimpl.
    + asimpl. unfold funcomp. rewrite rinstInst'_spec. now rewrite !IHphi2.
  - f_equal. f_equal. 2: f_equal.
    + rewrite idSubst_index; trivial. now intros [].
    + now asimpl.
    + erewrite ext_spec with (tau_prog := up_prog_prog (up_exp_prog (up_type_prog sigma))).
      now rewrite IHphi. 2: reflexivity. all: now intros [].
  - rewrite instId'_type. f_equal; now rewrite ttrans_E_subst_exp.
  - induction t in sigma |- *; cbn; trivial. f_equal. f_equal.
    + rewrite idSubst_type; trivial. now intros [].
    + rewrite idSubst_index; trivial. now intros [].
    + erewrite ext_spec with (tau_prog := up_prog_prog (up_exp_prog (up_type_prog sigma))).
      now rewrite trans_S_subst_spec. 2: reflexivity. all: now intros [].
Qed.

Lemma trans_SL_ren' Psi sigma n :
  trans_SL' (map (ren_form sigma) Psi) n = map (ren_spec sigma id sigma) (trans_SL' Psi n).
Proof.
  induction Psi in n |- *; cbn; trivial. now rewrite trans_S_ren, IHPsi.
Qed.

Lemma trans_SL_ren Psi sigma :
  trans_SL (map (ren_form sigma) Psi) = map (ren_spec sigma id sigma) (trans_SL Psi).
Proof.
  apply trans_SL_ren'.
Qed.



(** Translation well-formedness lemmas **)

Lemma trans_is_index Xi s t :
  has_kind Xi t s -> is_index Xi (trans_I s t).
Proof.
  induction s in Xi, t |- *.
  - apply ii_refb.
  - intros H. cbn. apply ii_univ. apply ii_ref.
    + apply hk_app with s; try now apply hk_var.
      eapply has_kind_ren; try apply H. intuition.
    + apply IHs. apply hk_var. reflexivity.
Qed.

Lemma trans_has_kind Xi phi :
  is_prop Xi phi -> has_kind Xi (trans_T phi) 0
with ttrans_has_kind Xi p s :
  has_sort Xi p s -> has_kind Xi (ttrans_T p) s.
Proof.
  - induction phi in Xi |- *; inversion 1; subst.
    + cbn. apply hk_arrow; try now apply IHphi1. now apply IHphi2.
    + cbn. apply hk_pi. apply hk_comp. now apply (IHphi (n :: Xi)).
    + cbn. apply hk_app with s; now apply ttrans_has_kind.
  - induction p in Xi |- *; inversion 1; subst.
    + cbn. now apply hk_var.
    + cbn. apply hk_abs. now apply trans_has_kind.
Qed.

Lemma trans_IL_length Xi n :
  length (trans_IL' Xi n) = length Xi.
Proof.
  induction Xi in n |- *; cbn; congruence.
Qed.

Lemma trans_IL_el Xi n i o :
  lup (trans_IL' Xi n) i = Some o -> exists s, lup Xi i = Some s.
Proof.
  intros H. destruct (lup Xi i) eqn: He; eauto.
  apply nth_error_None in He. rewrite <- (trans_IL_length _ n) in He.
  apply nth_error_None in He. congruence.
Qed.
  
Lemma trans_I_inj s s' t :
  trans_I s t = trans_I s' t -> s = s'.
Proof.
  induction s in s', t |- *; destruct s'; cbn; congruence.
Qed.

Lemma trans_IL_lup' Xi n s i :
  lup Xi i = Some s <-> lup (trans_IL' Xi n) i = Some (trans_I s (var_type (n+i))).
Proof.
  induction Xi in n, i |- *; destruct i; cbn; try intuition congruence.
  - rewrite <- plus_n_O. split; intros [=]; try congruence. now apply trans_I_inj in H0 as ->.
  - rewrite (@IHXi (S n) i). now rewrite <- plus_n_Sm.
Qed.

Lemma trans_IL_lup Xi s i :
  lup Xi i = Some s -> lup (trans_IL Xi) i = Some (trans_I s (var_type i)).
Proof.
  now rewrite (@trans_IL_lup' _ 0).
Qed.

Lemma trans_IL_up Xi n :
  list_map (ren_index ↑) (trans_IL' Xi n) = trans_IL' Xi (S n).
Proof.
  induction Xi in n |- *; cbn; trivial.
  rewrite IHXi. now rewrite trans_I_ren.
Qed.

Lemma trans_is_spec Xi phi Delta e :
  is_prop Xi phi -> has_type Xi Delta e (trans_T phi) -> is_spec Xi Delta (trans_IL Xi) (trans_S phi e)
with ttrans_has_index Xi p s Delta :
  has_sort Xi p s -> has_index Xi Delta (trans_IL Xi) (ttrans_E p) (trans_I s (ttrans_T p)).
Proof.
  induction phi in Xi, Delta, e |- *; inversion 1; subst; intros HT.
  - cbn. apply is_tmall, is_implies.
    + apply IHphi1; trivial. now apply ht_var.
    + apply is_after with (trans_T phi2).
      * rewrite rinstInst'_spec, trans_S_subst_spec. cbn. apply IHphi2; trivial. now apply ht_var.
      * apply ht_tmapp with (trans_T phi1).
        -- rewrite <- rinstId'_type. eapply has_type_ren; try apply HT; try tauto.
           cbn. intros. now rewrite rinstId'_type.
        -- apply ht_var. reflexivity.
  - cbn. apply is_tyall, is_spall; try now apply trans_is_index, hk_var.
    unfold trans_IL. rewrite trans_IL_up. apply is_after with (trans_T phi).
    + apply IHphi; trivial. now apply ht_var.
    + replace (comp (trans_T phi)) with ((comp (ren_type swap (trans_T phi)))[(0 __type)..]).
      * apply ht_tyapp with n; try now apply hk_var. cbn in HT.
        change (pi n (comp (ren_type swap (trans_T phi)))) with ((pi n (comp (trans_T phi))) ⟨↑⟩).
        eapply has_type_ren; try apply HT; try tauto. intros. now apply map_nth_error.
      * cbn. f_equal. asimpl. unfold funcomp. apply idSubst_type. now intros [].
  - cbn. eapply is_holds; try apply ttrans_has_index, H3; try apply HT.
    apply (ttrans_has_index _ _ _ Delta) in H2.
      cbn in H2. eapply (hi_exapp (t := ttrans_T t0)) in H2.
      * cbn in H2. rewrite trans_I_subst in H2. cbn in H2. now asimpl in H2.
      * now apply ttrans_has_kind.
  - induction p in Xi, Delta |- *; inversion 1; subst.
    + cbn. apply hi_var. now apply trans_IL_lup.
    + cbn. apply hi_exabs. eapply hi_conv.
      * apply ci_ref_type, ct_sym, ct_beta. reflexivity.
      * asimpl. unfold funcomp. rewrite idSubst_type; trivial; try now intros [].
        unfold trans_IL. rewrite trans_IL_up. apply hi_cexp.
        apply trans_is_spec; trivial. now apply ht_var.
Qed.



(** Soundness theorem **)

Lemma trans_SL_lup' Psi psi n i :
   lup Psi i = Some psi -> lup (trans_SL' Psi n) i = Some (trans_S psi (var_prog (n + i))).
Proof.
  induction Psi in n, i, psi |- *; destruct i; cbn; try intuition congruence.
  - rewrite <- plus_n_O. intros [=]. congruence.
  - intros H. rewrite (@IHPsi psi (S n) i); trivial. now rewrite <- plus_n_Sm.
Qed.

Lemma trans_SL_lup Psi psi i :
  lup Psi i = Some psi -> lup (trans_SL Psi) i = Some (trans_S psi (var_prog i)).
Proof.
  apply trans_SL_lup'.
Qed.

Lemma trans_SL_up Psi n :
  list_map (ren_spec id ↑ id) (trans_SL' Psi n) = trans_SL' Psi (S n).
Proof.
  induction Psi in n |- *; cbn; trivial.
  rewrite IHPsi. now rewrite rinstInst'_spec, trans_S_subst_spec.
Qed.

Lemma test t t' e e' Delta Gamma :
  has_type Delta Gamma e (comp (arrow t t')) -> has_type Delta Gamma e' (comp t)
  -> has_type Delta Gamma (bind e (bind (ren_prog id ↑ e') (tmapp (var_prog 1) (var_prog 0)))) (comp t').
Proof.
  intros H1 H2.
  apply ht_bind with (arrow t t'); trivial.
  apply ht_bind with t.
  - rewrite <- rinstId'_type. eapply has_type_ren; try apply H2; trivial.
    intros. now rewrite rinstId'_type.
  - apply ht_tmapp with t; now apply ht_var.
Qed.

Lemma is_value_ren e sig1 sig2 :
  is_value e -> is_value e⟨sig1;sig2⟩.
Proof.
  induction 1; cbn in *; econstructor; eauto.
Qed.

Lemma red_prog_ren e1 e2 sig1 sig2 :
  red_prog e1 e2 -> red_prog e1⟨sig1;sig2⟩ e2⟨sig1;sig2⟩.
Proof.
  induction 1; cbn in *.
  - econstructor 1; eauto.
  - econstructor 2. rewrite H. now asimpl.
  - econstructor 3.
    + rewrite H. now asimpl.
    + now apply is_value_ren.
  - econstructor 4. rewrite H. now asimpl.
  - econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto. now apply is_value_ren.
  - econstructor 8; eauto.
Qed.

Lemma conv_prog_ren e1 e2 sig1 sig2 :
  conv_prog e1 e2 -> conv_prog e1⟨sig1;sig2⟩ e2⟨sig1;sig2⟩.
Proof.
  induction 1.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto. now apply conv_type_ren.
Qed.

Lemma conv_spec_ren phi psi sig1 sig2 sig3 :
  conv_spec phi psi -> conv_spec phi⟨sig1;sig2;sig3⟩ psi⟨sig1;sig2;sig3⟩
with conv_exp_ren q q' sig1 sig2 sig3 :
  conv_exp q q' -> conv_exp q⟨sig1;sig2;sig3⟩ q'⟨sig1;sig2;sig3⟩.
Proof.
  induction 1 in sig1, sig2, sig3 |- *; cbn in *.
  - econstructor 1; eauto.
  - econstructor 2; eauto.
  - econstructor 3; eauto.
  - econstructor 4; eauto.
  - econstructor 5; eauto.
  - econstructor 6; eauto. now apply conv_prog_ren.
  - econstructor 7; eauto.
  - econstructor 8; eauto.
  - econstructor 9; eauto. now apply conv_type_ren.
  - econstructor 10; eauto.
  - econstructor 11; eauto. now apply conv_index_ren.
  - econstructor 12; eauto.
  - econstructor 13; eauto. now apply conv_prog_ren.
  - fold ren_exp. econstructor 14; eauto.
  - fold ren_exp. econstructor 15; eauto.
  - induction 1 in sig1, sig2, sig3 |- *; cbn in *.
    + econstructor 1; eauto.
    + econstructor 2; eauto.
    + econstructor 3; eauto.
    + econstructor 4; eauto. rewrite H. now asimpl.
    + econstructor 5; eauto.
    + econstructor 6; eauto. now apply conv_type_ren.
    + fold ren_exp. econstructor 7; eauto. now apply conv_type_ren.
    + fold ren_spec. econstructor 8; eauto. now apply conv_index_ren.
    + fold ren_spec. econstructor 9; eauto.
Qed.

Lemma HOPL_ren sig1 sig2 sig3 A phi :
  HOPL_prv A phi -> HOPL_prv (map (ren_spec sig1 sig2 sig3) A) (ren_spec sig1 sig2 sig3 phi).
Proof.
  induction 1 in sig1, sig2, sig3 |- * ; cbn in *.
  - constructor. now apply in_map.
  - econstructor 2. eauto.
  - econstructor 3; eauto.
  - econstructor 4. eapply HOPL_eq. 3: reflexivity.
    + apply IHHOPL_prv.
    + rewrite !map_map. apply map_ext. intros psi. now asimpl.
  - eapply HOPL_eq. 2: reflexivity.
    + econstructor 5 with (t := t⟨sig1⟩). apply IHHOPL_prv.
    + cbn. now asimpl.
  - econstructor 6. eapply HOPL_eq. 3: reflexivity.
    + apply IHHOPL_prv.
    + rewrite !map_map. apply map_ext. intros psi. now asimpl.
  - eapply HOPL_eq. 2: reflexivity.
    + econstructor 7 with (e := ren_prog sig1 sig2 e). apply IHHOPL_prv.
    + cbn. now asimpl.
  - econstructor 8. eapply HOPL_eq. 3: reflexivity.
    + apply IHHOPL_prv.
    + rewrite !map_map. apply map_ext. intros psi. now asimpl.
  - eapply HOPL_eq. 2: reflexivity.
    + econstructor 9 with (q := ren_exp sig1 sig2 sig3 q). apply IHHOPL_prv.
    + cbn. now asimpl.
  - econstructor 10. eapply HOPL_eq. 2: reflexivity.
    + apply IHHOPL_prv.
    + now asimpl.
  - eapply HOPL_eq. 2: reflexivity.
    + econstructor 11. apply IHHOPL_prv.
    + now asimpl.
  - constructor 12. eapply HOPL_eq. 2: reflexivity.
    + apply IHHOPL_prv.
    + now asimpl.
  - constructor 13. eapply HOPL_eq. 2: reflexivity.
    + apply IHHOPL_prv.
    + cbn. now asimpl.
  - econstructor 14. 2: apply IHHOPL_prv2. eapply HOPL_eq; try apply IHHOPL_prv1.
    2: reflexivity. f_equal. rewrite !map_map. apply map_ext. intros phi1. now asimpl.
  - eapply HOPL_eq with (phi := subst_spec var_type ((ren_prog sig1 sig2 e1)..) var_exp (ren_spec sig1 (upRen_prog_prog sig2) sig3 phi)).
    2: reflexivity. econstructor 15 with (e2 := ren_prog sig1 sig2 e2).
    + now apply red_prog_ren.
    + eapply HOPL_eq. 2: reflexivity. apply IHHOPL_prv. now asimpl.
    + now asimpl.
  - econstructor 16; try apply IHHOPL_prv. now apply conv_spec_ren.
Qed.

Theorem soundness' Psi psi :
  HOL_prv Psi psi -> exists e, HOPL_prv (trans_SL Psi) (after e (trans_S psi (var_prog 0))).
Proof.
  induction 1.
  - apply In_nth_error in H as [n Hn]. exists (ret (var_prog n)). apply HOPL_MI, HOPL_CTX.
    apply trans_SL_lup in Hn. apply nth_error_In in Hn. now rewrite trans_S_subst_spec.
  - destruct IHHOL_prv as [e He]. exists (ret (tmabs (trans_T phi) e)).
    apply HOPL_MI. cbn. asimpl. apply HOPL_EAI, HOPL_II. cbn in He.
    replace (after e (trans_S psi (var_prog 0))) with
      (subst_spec var_type (e..) var_exp (after (var_prog 0) (ren_spec id swap id (trans_S psi (var_prog 0))))) in He.
    + apply HOPL_RED with (e1 := tmapp (tmabs (trans_T phi) e ⟨id;swap⟩) (var_prog 0)) in He.
      * cbn in He. asimpl in He. eapply HOPL_eq; try apply He.
        -- rewrite !trans_S_subst_spec. f_equal. now rewrite <- trans_SL_up.
        -- f_equal. now rewrite !trans_S_subst_spec.
      * apply rp_betatm; try apply iv_var. asimpl. rewrite idSubst_prog; trivial. now intros [].
    + cbn. asimpl. unfold funcomp. f_equal. apply idSubst_spec; try now intros [].
  - destruct IHHOL_prv1 as [e1 H1], IHHOL_prv2 as [e2 H2].
    exists (bind e1 (bind e2 (tmapp (var_prog 0) (var_prog 1)))).
    apply HOPL_ME. eapply HOPL_MM; try apply H1. apply HOPL_ME.
    eapply HOPL_MM with (trans_S phi (var_prog 0)). 2: admit.
    eapply HOPL_IE. 2: apply HOPL_CTX; now left.
    eapply HOPL_eq. 2: reflexivity.
    eapply HOPL_EAE with (e := var_prog 1). apply HOPL_CTX. right. cbn. now left.
    cbn. asimpl. unfold funcomp. rewrite !trans_S_subst_spec. cbn. Search trans_S.
  - destruct IHHOL_prv as [e He]. exists (ret (tyabs s e)).
    apply HOPL_MI. cbn. asimpl. apply HOPL_TAI, HOPL_SAI.
    replace (after e (trans_S phi (var_prog 0))) with
      (subst_spec var_type (e..) var_exp (after (var_prog 0) (ren_spec id swap id (trans_S phi (var_prog 0))))) in He.
    + apply HOPL_RED with (e1 := tyapp (tyabs s e ⟨swap;id⟩) (var_type 0)) in He.
      * cbn in He. asimpl in He. erewrite map_map, map_ext, <- trans_SL_ren.
        -- rewrite trans_S_subst_spec in He. cbn in He. erewrite ext_spec.
           rewrite trans_S_subst_spec. 2,4: now intros []. 2: reflexivity. cbn. apply He.
        -- intros psi. now asimpl.
      * apply rp_betaty. asimpl. rewrite idSubst_prog; trivial. now intros [].
    + cbn. asimpl. unfold funcomp. f_equal. apply idSubst_spec; now intros [].
  - destruct IHHOL_prv as [e He]. exists (bind e (tyapp (var_prog 0) (ttrans_T p))).
    apply HOPL_ME. eapply HOPL_MM; try apply He. cbn.
    eapply HOPL_eq. eapply HOPL_SAE with (q := ttrans_E p).
    eapply HOPL_eq. eapply HOPL_TAE with (t := ttrans_T p).
    2,4: reflexivity. apply HOPL_CTX. now left.
    + cbn. reflexivity.
    + cbn. f_equal.
      * now asimpl.
      * rewrite substSubst_spec, <- trans_S_subst. apply ext_spec; intros []; cbn; trivial.
        -- now asimpl.
        -- now rewrite rinstInst'_exp, ttrans_E_subst_exp.
  - destruct IHHOL_prv as [e He]. exists e. eapply HOPL_MM; eauto. cbn. eapply HOPL_CONV.
    + apply cs_sym, cs_holds_exp1, ce_beta. reflexivity.
    + cbn. apply HOPL_CI. asimpl. apply HOPL_CTX. left.
      change (var_prog 0) with (subst_prog var_type (var_prog 0 .: var_prog) (var_prog 0)).
      rewrite <- trans_S_subst_spec, <- trans_S_subst. asimpl. unfold funcomp.
      apply ext_spec; trivial. intros []; trivial. now rewrite ttrans_E_subst_exp.
  - destruct IHHOL_prv as [e He]. exists e. eapply HOPL_MM; eauto. cbn. eapply HOPL_IE.
    + eapply HOPL_CONV; try (apply HOPL_CTX; now left). now apply cs_holds_exp1, ce_beta.
    + cbn. apply HOPL_II. eapply HOPL_IE.
      * eapply HOPL_CE. apply HOPL_CTX. now left.
      * apply HOPL_II, HOPL_CTX. left. asimpl. unfold funcomp.
        change (var_prog 0) with (subst_prog var_type (var_prog 0 .: var_prog) (var_prog 0)) at 3.
        rewrite <- trans_S_subst_spec, <- trans_S_subst. asimpl. unfold funcomp.
        apply ext_spec; trivial. intros []; trivial. now rewrite ttrans_E_subst_exp.
Admitted.

Theorem soundness Xi Psi psi :
  (forall psi', In psi' (psi :: Psi) -> is_prop Xi psi') -> HOL_prv Psi psi
  -> exists p, has_type Xi (map trans_T Psi) p (comp (trans_T psi)) /\ HOPL_prv (trans_SL Psi) (after p (trans_S psi)).
Proof.
Admitted.
  
