Set Implicit Arguments.
Unset Strict Implicit.

Require Import List.
Require Import core unscoped hopl.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.

Notation lup := nth_error.



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
| ht_tmabs e t1 t2 : has_type Delta (t1 :: Gamma) e t2
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
                         -> has_type Delta Gamma (tmapp e1 e2) t2.

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
| hi_cexp' phi t t1 t2 k o : is_spec Delta (t :: Gamma) (o :: Sigma) phi
                           -> t = t1[t2..]
                           -> has_index Delta Gamma Sigma (cexp t o phi) (ref (app (abs k t1) t2) o)

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
| HOL_IE phi psi : HOL_prv A phi -> HOL_prv A (implies phi psi) -> HOL_prv A psi
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
| HOPL_IE phi psi : HOPL_prv A phi
                -> HOPL_prv A (spimplies phi psi)
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
                -> HOPL_prv A (after e phi)
| HOPL_ME phi e1 e2 : HOPL_prv A (after e1 (after e2 phi))
                    -> HOPL_prv A (after (bind e1 e2) phi)
| HOPL_MM phi psi e : HOPL_prv (phi :: A) psi
                  -> HOPL_prv A (after e phi)
                  -> HOPL_prv A (after e psi).

Lemma HOPL_weak A A' phi :
  HOPL_prv A phi -> incl A A' -> HOPL_prv A' phi.
Proof.
  induction 1 in A' |- *; intros HA.
  all: try unshelve (solve [econstructor; auto with datatypes]); try now econstructor.
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

Lemma trans_form_is_prop Delta Gamma Sigma phi :
  is_spec Delta Gamma Sigma phi -> is_prop (map trans_sort Sigma) (trans_form phi)
with trans_term_has_sort Delta Gamma Sigma q o :
  has_index Delta Gamma Sigma q o -> has_sort (map trans_sort Sigma) (trans_term q) (trans_sort o).
Proof.
  induction phi in Delta, Gamma, Sigma |- *; cbn; inversion 1; subst.
  - apply ip_holds with (trans_sort o).
    + now apply trans_term_has_sort in H4.
    + now apply trans_term_has_sort in H5.
  - apply ip_implies; try eapply IHphi1; try eapply IHphi2; eassumption.
  - now apply IHphi in H2.
  - apply IHphi in H1. erewrite map_map, map_ext in H1; try apply H1.
    intros. apply trans_sort_ren.
  - now apply IHphi in H1.
  - apply ip_all. now apply IHphi in H2.
  - induction q in Delta, Gamma, Sigma, o |- *; cbn; inversion 1; subst.
    + apply hs_var. now apply map_nth_error.
    + apply hs_cterm. now apply trans_form_is_prop in H4.
    + apply hs_cterm. now apply trans_form_is_prop in H4.
    + apply IHq in H3. erewrite map_map, map_ext in H3; try apply H3.
    intros. apply trans_sort_ren.
    + rewrite trans_sort_subst. now apply IHq in H2.
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
  - assumption.
  - eapply HOL_IE; try apply IHHOPL_prv2. apply HOL_II, IHHOPL_prv1.
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

Lemma has_type_ren Delta Delta' Gamma Gamma' xi rho e t :
  has_type Delta Gamma e t
  -> (forall n k, lup Delta n = Some k -> lup Delta' (xi n) = Some k)
  -> (forall n t', lup Gamma n = Some t' -> lup Gamma' (rho n) = Some (ren_type xi t'))
  -> has_type Delta' Gamma' (ren_prog xi rho e) (ren_type xi t).
Proof.
  induction e in Delta, Gamma, xi, rho, Delta', Gamma', t |- *; inversion 1; subst; intros HD HG; cbn.
  - apply ht_var. now apply HG.
  - apply ht_tyabs. eapply IHe; try apply H3.
    + intros []; cbn; intuition.
    + intros n0 t' H0. rewrite nth_error_map in H0.
      destruct (lup Gamma n0) eqn: He; cbn in *; try discriminate.
      injection H0 as []. erewrite renRen_type, extRen_type, <- renRen_type.
      * apply map_nth_error. now apply HG.
      * now intros [].
  - apply ht_tmabs. eapply IHe; try apply H3.
    + intros []; cbn; intuition.
    + intros []; cbn; try congruence. apply HG.
  - cbn. asimpl. erewrite ext_type, <- renSubst_type at 1.
    + apply ht_tyapp with k.
      * eapply IHe in H2; eauto.
      * eapply has_kind_ren; try apply H4. apply HD.
    + now intros [].
  - apply ht_tmapp with t1⟨xi⟩; eapply IHe2 in H4; eauto. eapply IHe1 in H2; eauto.
  - apply ht_ret. eapply IHe; eauto.
  - apply ht_bind with t1⟨xi⟩. eapply IHe1 in H2; eauto. eapply IHe2 in H4; eauto.
    intros []; cbn; intuition. unfold upRen_prog_type. now injection H0 as ->.
Qed.

Lemma is_index_ren Delta Delta' xi o :
  is_index Delta o
  -> (forall n k, lup Delta n = Some k -> lup Delta' (xi n) = Some k)
  -> is_index Delta' o⟨xi⟩.
Proof.
  induction o in Delta, Delta', xi |- *; inversion 1; subst; intros HD; cbn.
  - apply ii_refb. now apply (has_kind_ren H1).
  - apply ii_ref; try now apply (has_kind_ren H2). now eapply IHo; try apply H3.
  - apply ii_univ. eapply IHo; try apply H1. intros []; cbn in *; intuition.
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
  induction phi in Delta, Gamma, Sigma, Delta', Gamma', Sigma', tren, pren, eren |- *;
    inversion 1; subst; intros HD HG HS; cbn.
  - eapply is_holds.
    + eapply has_type_ren; try apply H3; intuition.
    + eapply has_index_ren in H4; eauto.
    + fold ren_index. eapply has_index_ren in H5; eauto.
  - apply is_implies; eauto.
  - apply is_after with t⟨tren⟩.
    + eapply IHphi; eauto. destruct n; cbn in *; intuition. now injection H0 as ->.
    + eapply has_type_ren in H3; eauto.
  - apply is_tyall. eapply IHphi; eauto.
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
  - apply is_tmall. eapply IHphi; eauto.
    intros [] t0; cbn; try apply HG.
    intros [=]; subst. reflexivity.
  - apply is_spall; try eapply is_index_ren; eauto. eapply IHphi; try apply H2; intuition.
    destruct n; cbn in *; intuition. now injection H0 as ->.
  - induction q in o, Delta, Gamma, Sigma, Delta', Gamma', Sigma', tren, pren, eren |- *;
      inversion 1; subst; intros HD HG HS; cbn.
    + apply hi_var. now apply HS.
    + apply hi_cexp. eapply is_spec_ren; try apply H4; intuition.
      * destruct n; cbn in *; intuition. now injection H0 as ->.
      * destruct n; cbn in *; intuition. now injection H0 as ->.
    + apply hi_cexp'.
      * eapply is_spec_ren; try apply H4; intuition.
        -- destruct n; cbn in *; intuition. now injection H0 as ->.
        -- destruct n; cbn in *; intuition. now injection H0 as ->.
      * now asimpl.
    + apply hi_exabs. eapply IHq; try apply H3; intuition.
      * destruct n0; cbn in *; intuition.
      * rewrite nth_error_map in H0.
        destruct (lup Gamma n0) eqn: He; cbn in *; try discriminate.
        injection H0 as []. erewrite renRen_type, extRen_type, <- renRen_type.
        -- apply map_nth_error. now apply HG.
        -- now intros [].
      * rewrite nth_error_map in H0.
        destruct (lup Sigma n0) eqn: He; cbn in *; try discriminate.
        injection H0 as []. erewrite renRen_index, extRen_index, <- renRen_index.
        -- apply map_nth_error. now apply HS.
        -- now intros [].
    + erewrite compSubstRen_index, ext_index, <- compRenSubst_index. eapply hi_exapp.
      eapply IHq in H2; try apply H2; intuition. 2,3: reflexivity.
      * eapply has_kind_ren; eauto.
      * now intros [].
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
  | implies phi psi => arrow (trans_T phi) (comp (trans_T psi))
  | all s phi => pi s (comp (trans_T phi))
  | holds p p' => app (ttrans_T p) (ttrans_T p')
  end
with ttrans_T (p : term) : type :=
  match p with 
  | var_term x => var_type x
  | cterm s phi => abs s (trans_T phi)
  end.

Definition swap := 0 .: (↑ >> ↑).

Fixpoint trans_S (phi : form) : spec :=
  match phi with
  | implies phi psi => tmall (trans_T phi)
                    (spimplies (trans_S phi)
                               (after (tmapp (var_prog 1) (var_prog 0))
                                      (trans_S psi)))
  | all s phi => tyall s
                    (spall (trans_I s (var_type 0))
                           (after (tyapp (var_prog 0) (var_type 0))
                                  (ren_spec id swap id (trans_S phi))))
  | holds p p' => spholds (exapp (ttrans_E p) (ttrans_T p')) (ttrans_E p') (var_prog 0)
  end
with ttrans_E (p : term) : exp :=
  match p with
  | var_term x => var_exp x
  | cterm s phi => exabs s (cexp (trans_T phi) (trans_I s (var_type 0)) (trans_S phi))
  end.



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
    + cbn. apply hk_arrow; try now apply IHphi1. now apply hk_comp, IHphi2.
    + cbn. apply hk_pi. apply hk_comp. now apply (IHphi (n :: Xi)).
    + cbn. apply hk_app with s; now apply ttrans_has_kind.
  - induction p in Xi |- *; inversion 1; subst.
    + cbn. now apply hk_var.
    + cbn. apply hk_abs. now apply trans_has_kind.
Qed.

Fixpoint trans_IL' (SL : list sort) n : list index :=
  match SL with
  | nil => nil
  | s :: SL => (trans_I s (var_type n)) :: trans_IL' SL (S n)
  end.

Definition trans_IL SL :=
  trans_IL' SL 0.

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

Lemma trans_is_spec Xi phi Delta :
  is_prop Xi phi -> is_spec Xi (trans_T phi :: Delta) (trans_IL Xi) (trans_S phi)
with ttrans_has_index Xi p s Delta :
  has_sort Xi p s -> has_index Xi Delta (trans_IL Xi) (ttrans_E p) (trans_I s (ttrans_T p)).
Proof.
  induction phi in Xi, Delta |- *; inversion 1; subst.
  - cbn. apply is_tmall, is_implies.
    + now apply IHphi1.
    + apply is_after with (trans_T phi2).
      * now apply IHphi2.
      * apply ht_tmapp with (trans_T phi1).
        -- apply ht_var. reflexivity.
        -- apply ht_var. reflexivity.
  - cbn. apply is_tyall, is_spall; try now apply trans_is_index, hk_var.
    unfold trans_IL. rewrite trans_IL_up. apply is_after with (trans_T phi).
    + cbn. apply (IHphi _ (map (ren_type ↑) Delta)) in H1. cbn in H1.
      eapply is_spec_ren'; try apply H1. now intros [] t.
    + replace (comp (trans_T phi)) with ((comp (trans_T phi)⟨upRen_type_type ↑⟩)[(0 __type)..]) at 2.
      * apply ht_tyapp with n; try now apply hk_var. now apply ht_var.
      * cbn. f_equal. asimpl. unfold funcomp. apply idSubst_type. now intros [].
  - cbn. eapply is_holds; try apply ttrans_has_index, H3.
    + apply ht_var. cbn. reflexivity.
    + apply (ttrans_has_index _ _ _ (app (ttrans_T t) (ttrans_T t0) :: Delta)) in H2.
      cbn in H2. eapply (hi_exapp (t := ttrans_T t0)) in H2.
      * cbn in H2. rewrite trans_I_subst in H2. cbn in H2. now asimpl in H2.
      * now apply ttrans_has_kind.
  - induction p in Xi, Delta |- *; inversion 1; subst.
    + cbn. apply hi_var. now apply trans_IL_lup.
    + cbn. apply hi_exabs. apply hi_cexp'.
      * unfold trans_IL. rewrite trans_IL_up. now apply trans_is_spec.
      * asimpl. unfold funcomp. rewrite idSubst_type; trivial. now intros [].
Qed.
