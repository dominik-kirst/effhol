(** * Translation from HOL to EffHOL **)

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

Fixpoint trans_S (phi : form) (e : prog) : spec :=
  match phi with
  | implies phi psi => tmall (trans_T phi)
                        (spimplies (trans_S phi (var_prog 0))
                                   (after (tmapp (ren_prog id ↑ e) (var_prog 0))
                                          (ren_spec id swap id (trans_S psi (var_prog 0)))))
  | all s phi => tyall s (spall (trans_I s (var_type 0))
                             (after (tyapp (ren_prog ↑ id e) (var_type 0))
                                    (ren_spec id swap id (trans_S phi (var_prog 0)))))
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



(** ** Translation substitution lemmas **)

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

Lemma trans_S_ren phi e sigma rho :
  ren_spec rho sigma rho (trans_S phi e) = trans_S (ren_form rho phi) (ren_prog rho sigma e)
with ttrans_E_ren t sigma rho :
  ren_exp rho sigma rho (ttrans_E t) = ttrans_E (ren_term rho t).
Proof.
  induction phi in e, sigma, rho |- *; cbn.
  - rewrite trans_T_ren. f_equal. f_equal.
    + rewrite IHphi1. reflexivity.
    + f_equal. now asimpl. change (var_prog 0) with ((ren_prog rho id (var_prog 0))) at 2.
      rewrite <- IHphi2. asimpl. unfold funcomp. now rewrite !IHphi2.
  - f_equal. f_equal; try apply trans_I_ren. asimpl. unfold funcomp. f_equal.
    change (var_prog 0) with ((ren_prog (upRen_prog_prog rho) id (var_prog 0))) at 2.
    rewrite <- IHphi. asimpl. unfold funcomp. now rewrite !IHphi.
  - now rewrite !ttrans_E_ren, ttrans_T_ren.
  - induction t in sigma |- *; cbn; trivial. f_equal. f_equal.
    + now rewrite trans_T_ren.
    + now rewrite trans_I_ren.
    + asimpl. unfold funcomp. now rewrite trans_S_ren.
Qed.

Lemma trans_S_subst phi e sigma rho :
  subst_spec (sigma >> ttrans_T) rho (sigma >> ttrans_E) (trans_S phi e)
  = trans_S (subst_form sigma phi) (subst_prog (sigma >> ttrans_T) rho e)
with ttrans_E_subst t sigma rho :
  subst_exp (sigma >> ttrans_T) rho (sigma >> ttrans_E) (ttrans_E t)
  = ttrans_E (subst_term sigma t).
Proof.
  induction phi in e, sigma, rho |- *; cbn.
  - f_equal. 2: f_equal. 3: f_equal.
    + now rewrite trans_T_subst.
    + change (var_prog 0) with (subst_prog (sigma >> ttrans_T) (up_prog_prog rho) (var_prog 0)).
      rewrite <- IHphi1. asimpl. unfold funcomp. apply ext_spec; try now intros [].
      intros n. rewrite ttrans_E_ren. now asimpl.
    + now asimpl.
    + change (var_prog 0) with (subst_prog (sigma >> ttrans_T) (up_prog_prog rho) (var_prog 0)).
      rewrite <- IHphi2. asimpl. unfold funcomp. apply ext_spec; try now intros [].
      intros n. rewrite !ttrans_E_ren. now asimpl.
  - f_equal. f_equal; try apply trans_I_subst. asimpl. unfold funcomp. f_equal.
    erewrite ext_spec, IHphi. rewrite trans_S_ren. cbn.
    3: reflexivity. cbn. rewrite rinstId'_form. reflexivity.
    + intros []; cbn; trivial. apply ttrans_T_ren.
    + intros []; cbn; trivial. now rewrite ttrans_E_ren.
  - now rewrite !ttrans_E_subst, ttrans_T_subst.
  - induction t in sigma |- *; cbn; trivial. f_equal. f_equal.
    + rewrite <- trans_T_subst. asimpl. unfold funcomp. cbn. apply ext_type.
      intros []; cbn; trivial. now rewrite ttrans_T_ren.
    + now rewrite trans_I_subst.
    + asimpl. unfold funcomp.
      set (sigma' := var_term 0 .: (fun x : nat => (sigma x) ⟨↑⟩)).
      set (rho' := var_prog 0 .: (fun x : nat => (rho x) ⟨↑;↑⟩)).
      change (var_prog 0) with (subst_prog (sigma' >> ttrans_T) rho' (var_prog 0)) at 3.
      rewrite <- trans_S_subst. apply ext_spec; intros []; cbn; trivial.
      * asimpl. apply ttrans_T_ren.
      * rewrite !ttrans_E_ren. now asimpl.
Qed.

Lemma trans_S_subst' phi x sigma :
  subst_spec (sigma >> ttrans_T) var_prog (sigma >> ttrans_E) (trans_S phi (var_prog x))
  = trans_S (subst_form sigma phi) (var_prog x).
Proof.
  now rewrite trans_S_subst.
Qed.

Lemma trans_S_subst_spec phi e rho :
  subst_spec var_type rho var_exp (trans_S phi e)
  = trans_S phi (subst_prog var_type rho e).
Proof.
  replace phi with (phi[var_term]) at 2.
  - now rewrite <- trans_S_subst.
  - now asimpl.
Qed.

Lemma ttrans_E_subst_exp t rho :
  subst_exp var_type rho var_exp (ttrans_E t)
  = ttrans_E t.
Proof.
  replace t with (t[var_term]) at 2.
  - now setoid_rewrite <- (@ttrans_E_subst t var_term rho).
  - now asimpl.
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



(** ** Translation well-formedness lemmas **)

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
    + cbn. apply hk_arrow; try now apply IHphi1. apply hk_comp. now apply IHphi2.
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
    + rewrite rinstInst'_spec, trans_S_subst_spec. apply IHphi; trivial. now apply ht_var.
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
      * apply ci_ref_type. constructor 3. constructor 1. apply ct_beta. reflexivity.
      * asimpl. unfold funcomp. rewrite idSubst_type; trivial; try now intros [].
        unfold trans_IL. rewrite trans_IL_up. apply hi_cexp.
        apply trans_is_spec; trivial. now apply ht_var.
Qed.



(** ** Soundness theorem **)

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

Lemma soundness_typing_check Xi Psi psi p :
  is_prop Xi psi
  -> has_type Xi (map trans_T Psi) p (comp (trans_T psi))
  -> is_spec Xi (map trans_T Psi) (trans_IL Xi) (after p (trans_S psi (var_prog 0))).
Proof.
  intros H1 H2. eapply is_after; eauto.
  apply trans_is_spec; trivial. now apply ht_var.
Qed.

Theorem soundness Xi Psi psi :
  THOL_prv Xi Psi psi
    -> exists p, has_type Xi (map trans_T Psi) p (comp (trans_T psi))
      /\ HOPL_prv (trans_SL Psi) (after p (trans_S psi (var_prog 0))).
Proof.
  induction 1.

  - (* Assumption *)
    apply In_nth_error in H as [n Hn].
    exists (ret (var_prog n)). split.
    {
      apply ht_ret. apply ht_var. now apply map_nth_error.
    }
    apply HOPL_MI, HOPL_CTX. apply trans_SL_lup in Hn.
    apply nth_error_In in Hn. now rewrite trans_S_subst_spec.

  - (* Implication introduction *)
    destruct IHTHOL_prv as [e [Ht He]].
    exists (ret (tmabs (trans_T phi) e)). split.
    {
      cbn. apply ht_ret. apply ht_tmabs. apply Ht.
    }
    apply HOPL_MI. cbn. asimpl. apply HOPL_EAI, HOPL_II. cbn in He.
    replace (after e (trans_S psi (var_prog 0))) with
      (subst_spec var_type (e..) var_exp (after (var_prog 0) (ren_spec id swap id (trans_S psi (var_prog 0))))) in He.
    + apply HOPL_RED with (e1 := tmapp (tmabs (trans_T phi) e ⟨id;swap⟩) (var_prog 0)) in He.
      * cbn in He. asimpl in He. eapply HOPL_eq; try apply He.
        -- rewrite !trans_S_subst_spec. f_equal. now rewrite <- trans_SL_up.
        -- f_equal. now rewrite !trans_S_subst_spec.
      * apply rp_betatm; try apply iv_var. asimpl. rewrite idSubst_prog; trivial. now intros [].
    + cbn. asimpl. unfold funcomp. f_equal. apply idSubst_spec; try now intros [].

  - (* Implication elimination *)
    destruct IHTHOL_prv1 as [e1 [Ht1 H1]], IHTHOL_prv2 as [e2 [Ht2 H2]].
    exists (bind e1 (bind e2⟨id;S⟩ (tmapp (var_prog 1) (var_prog 0)))). split.
    {
      eapply ht_bind; try apply Ht1. apply ht_bind with ((trans_T phi)⟨id⟩).
      + eapply has_type_ren in Ht2. refine Ht2. tauto. cbn. now asimpl.
      + eapply ht_tmapp; apply ht_var; cbn. reflexivity. now asimpl.
    }
    apply HOPL_ME. eapply HOPL_MM; try apply H1. apply HOPL_ME.
    eapply HOPL_MM with (trans_S phi (var_prog 0)).
    2: { eapply HOPL_weak. eapply HOPL_eq. apply (@HOPL_ren id S id). apply H2.
         reflexivity. cbn. now rewrite rinstInst'_spec, trans_S_subst_spec. firstorder. }
    eapply HOPL_IE. 2: apply HOPL_CTX; now left.
    eapply HOPL_eq. 2: reflexivity.
    eapply HOPL_EAE with (e := var_prog 0). apply HOPL_CTX.
    right. cbn. now left. cbn. asimpl. unfold funcomp.
    now rewrite rinstInst'_spec, !trans_S_subst_spec.

  - (* Universal introduction *)
    destruct IHTHOL_prv as [e [Ht He]].
    exists (ret (tyabs s e)). split.
    { 
      cbn. apply ht_ret. apply ht_tyabs. rewrite map_map in *.
      erewrite map_ext; try apply Ht. intros psi. now rewrite trans_T_ren.
    }
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

  - (* Universal elimination *)
    destruct IHTHOL_prv as [e [Ht He]].
    exists (bind e (tyapp (var_prog 0) (ttrans_T p))). split.
    {
      eapply ht_bind; try apply Ht.
      replace (comp (trans_T phi[p..])) with ((comp (trans_T phi))[(ttrans_T p)..]).
      - apply ht_tyapp with s; try now apply ht_var. apply ttrans_has_kind. apply H0.
      - rewrite <- trans_T_subst. cbn. f_equal. apply ext_type. now intros [].
    }
    apply HOPL_ME. eapply HOPL_MM; try apply He. cbn.
    eapply HOPL_eq. eapply HOPL_SAE with (q := ttrans_E p).
    eapply HOPL_eq. eapply HOPL_TAE with (t := ttrans_T p).
    2,4: reflexivity. apply HOPL_CTX. now left.
    + cbn. reflexivity.
    + cbn. f_equal.
      * now asimpl.
      * rewrite substSubst_spec, <- trans_S_subst'.
        rewrite !substRen_spec, renSubst_spec.
        apply ext_spec; intros []; cbn; trivial.
        -- now asimpl.
        -- now rewrite !ttrans_E_ren.

  - (* Comprehension introduction *)
    destruct IHTHOL_prv as [e [Ht He]].
    exists e. split.
    {
      cbn. eapply ht_conv; try apply Ht. constructor 3. constructor 1. apply ct_comp, ct_beta. cbn.
      rewrite <- trans_T_subst. cbn. f_equal. apply ext_type. now intros [].
    }
    eapply HOPL_MM; eauto. cbn. eapply HOPL_CONV.
    + apply cs_sym, cs_holds_exp1, ce_beta. reflexivity.
    + cbn. apply HOPL_CI. asimpl. apply HOPL_CTX. left.
      change (var_prog 0) with (subst_prog var_type (var_prog 0 .: var_prog) (var_prog 0)).
      rewrite <- trans_S_subst_spec, <- trans_S_subst'. asimpl. unfold funcomp.
      apply ext_spec; trivial. intros []; trivial. cbn. now rewrite ttrans_E_subst_exp.

  - (* Comprehension elimination *)
    destruct IHTHOL_prv as [e [Ht He]].
    exists e. split.
    {
      cbn in Ht. eapply ht_conv; try apply Ht. constructor 1. apply ct_comp, ct_beta. cbn.
      rewrite <- trans_T_subst. cbn. f_equal. apply ext_type. now intros [].
    }
    eapply HOPL_MM; eauto. cbn.
    eapply HOPL_eq. 2: reflexivity. eapply HOPL_CE. eapply HOPL_CONV.
    eapply cs_holds_exp1. eapply ce_beta. 2: apply HOPL_CTX; now left.
    cbn. reflexivity. asimpl. unfold funcomp.
    change (var_prog 0) with (subst_prog var_type (var_prog 0 .: var_prog) (var_prog 0)) at 3.
    rewrite <- trans_S_subst_spec, <- trans_S_subst'. asimpl. unfold funcomp.
    apply ext_spec; trivial. intros []; trivial. now rewrite ttrans_E_subst_exp.
Qed.

Print Assumptions soundness.
  
