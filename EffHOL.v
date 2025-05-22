(** * Specification of EffHOL *)

Set Implicit Arguments.
Unset Strict Implicit.

From Coq.Relations Require Import Relation_Operators.

Require Import List.
Require Import core unscoped syntax.

Import RenNotations.
Import SubstNotations.
Import CombineNotations.
Import UnscopedNotations.



(** ** Reduction and conversion **)

Inductive is_value : prog -> Prop :=
| iv_var x : is_value (var_prog x)
| iv_tyabs k e : is_value (tyabs k e)
| iv_tmabs t e : is_value (tmabs t e).
(*| iv_ret e : is_value (ret e).*)

Inductive red_prog : prog -> prog -> Prop :=
(*| rp_trans e1 e2 e3 : red_prog e1 e2 -> red_prog e2 e3 -> red_prog e1 e3*)
| rp_betaty k e t t' : t' = subst_prog (t..) var_prog e -> red_prog (tyapp (tyabs k e) t) t'
| rp_betatm t e1 e2 e : e = subst_prog var_type (e2..) e1 -> is_value e2 -> red_prog (tmapp (tmabs t e1) e2) e
| rp_ret e1 e2 e : e = subst_prog var_type (e1..) e2 -> red_prog (bind (ret e1) e2) e.
(*| rp_tyapp e1 e2 t : red_prog e1 e2 -> red_prog (tyapp e1 t) (tyapp e2 t)
| rp_tmapp1 e1 e2 e : red_prog e1 e2 -> red_prog (tmapp e1 e) (tmapp e2 e)
| rp_tmapp2 e1 e2 e : red_prog e1 e2 -> is_value e -> red_prog (tmapp e e1) (tmapp e e2)
| rp_bind e1 e2 e : red_prog e1 e2 -> red_prog (bind e1 e) (bind e2 e).*)

Inductive tred_type : type -> type -> Prop :=
| ct_beta k t1 t2 t : t = subst_type (t2..) t1 -> tred_type (app (abs k t1) t2) t
| ct_abs k t1 t2 : tred_type t1 t2 -> tred_type (abs k t1) (abs k t2)
| ct_app1 t1 t2 t : tred_type t1 t2 -> tred_type (app t1 t) (app t2 t)
| ct_app2 t1 t2 t : tred_type t1 t2 -> tred_type (app t t1) (app t t2)
| ct_arrow1 t1 t2 t : tred_type t1 t2 -> tred_type (arrow t1 t) (arrow t2 t)
| ct_arrow2 t1 t2 t : tred_type t1 t2 -> tred_type (arrow t t1) (arrow t t2)
| ct_pi t1 t2 k : tred_type t1 t2 -> tred_type (pi k t1) (pi k t2)
| ct_comp t1 t2 : tred_type t1 t2 -> tred_type (comp t1) (comp t2).

Definition conv_type :=
  clos_refl_sym_trans _ tred_type.

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



(** ** Reduction and conversion renaming lemmas **)

Lemma is_value_ren e sig1 sig2 :
  is_value e -> is_value e⟨sig1;sig2⟩.
Proof.
  destruct 1; cbn in *; econstructor; eauto.
Qed.

Lemma red_prog_ren e1 e2 sig1 sig2 :
  red_prog e1 e2 -> red_prog e1⟨sig1;sig2⟩ e2⟨sig1;sig2⟩.
Proof.
  induction 1; cbn in *.
  (*- econstructor 1; eauto.*)
  - econstructor 1. rewrite H. now asimpl.
  - econstructor 2.
    + rewrite H. now asimpl.
    + now apply is_value_ren.
  - econstructor 3. rewrite H. now asimpl.
  (*- econstructor 5; eauto.
  - econstructor 6; eauto.
  - econstructor 7; eauto. now apply is_value_ren.
  - econstructor 8; eauto.*)
Qed.

Lemma tred_type_ren t1 t2 xi :
  tred_type t1 t2 -> tred_type t1⟨xi⟩ t2⟨xi⟩.
Proof.
  induction 1 in xi |-*; cbn.
  - apply ct_beta. rewrite H. now asimpl.
  - now apply ct_abs.
  - now apply ct_app1.
  - now apply ct_app2.
  - now apply ct_arrow1.
  - now apply ct_arrow2.
  - now apply ct_pi.
  - now apply ct_comp.
Qed.

Lemma conv_type_ren t1 t2 xi :
  conv_type t1 t2 -> conv_type t1⟨xi⟩ t2⟨xi⟩.
Proof.
  induction 1 in xi |-*; cbn.
  - constructor. now apply tred_type_ren.
  - constructor 2.
  - constructor 3. apply IHclos_refl_sym_trans.
  - econstructor 4; [apply IHclos_refl_sym_trans1 | apply IHclos_refl_sym_trans2].
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



(** ** Reduction and conversion substitution lemmas **)

Lemma tred_type_subst t1 t2 xi :
  tred_type t1 t2 -> tred_type t1[xi] t2[xi].
Proof.
  induction 1 in xi |-*; cbn.
  - apply ct_beta. rewrite H. now asimpl.
  - now apply ct_abs.
  - now apply ct_app1.
  - now apply ct_app2.
  - now apply ct_arrow1.
  - now apply ct_arrow2.
  - now apply ct_pi.
  - now apply ct_comp.
Qed.

Lemma conv_type_subst t1 t2 xi :
  conv_type t1 t2 -> conv_type t1[xi] t2[xi].
Proof.
  induction 1 in xi |-*; cbn.
  - constructor. now apply tred_type_subst.
  - constructor 2.
  - constructor 3. apply IHclos_refl_sym_trans.
  - econstructor 4; [apply IHclos_refl_sym_trans1 | apply IHclos_refl_sym_trans2].
Qed.



(** ** Typing judgements **)

Notation lup := nth_error.

Lemma lup_map_el X Y (f : X -> Y) L n y :
  lup (map f L) n = Some y -> exists x, lup L n = Some x /\ y = f x.
Proof.
  revert L. induction n; destruct L; cbn.
  - discriminate.
  - intros [=]; subst. now exists x.
  - discriminate.
  - apply IHn.
Qed.

Definition kind := nat.

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
                     -> has_type Delta Gamma (tmabs t1 e) (arrow t1 (comp t2))
| ht_ret e t : has_type Delta Gamma e t
               -> has_type Delta Gamma (ret e) (comp t)
| ht_bind e1 e2 t1 t2 : has_type Delta Gamma e1 (comp t1)
                        -> has_type Delta (t1 :: Gamma) e2 (comp t2)
                        -> has_type Delta Gamma (bind e1 e2) (comp t2)
| ht_tyapp e t1 t2 k : has_type Delta Gamma e (pi k t1)
                       -> has_kind Delta t2 k
                       -> has_type Delta Gamma (tyapp e t2) t1[t2..]
| ht_tmapp e1 e2 t1 t2 : has_type Delta Gamma e1 (arrow t1 (comp t2))
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



(** ** Judgement weakening lemmas **)

Lemma lup_app X (A B : list X) n x :
  lup A n = Some x -> lup (A ++ B) n = Some x.
Proof.
  intros H. rewrite nth_error_app1; trivial. apply nth_error_Some. congruence.
Qed.

Lemma has_kind_weak Delta Delta' t k :
  has_kind Delta t k -> has_kind (Delta ++ Delta') t k.
Proof.
  induction 1; cbn; try now (econstructor; eauto).
  constructor. now apply lup_app.
Qed.

Lemma has_type_weak Delta Delta' Gamma Gamma' e t :
  has_type Delta Gamma e t -> has_type (Delta ++ Delta') (Gamma ++ Gamma') e t.
Proof.
  induction 1 in Delta', Gamma' |- *; cbn; try now (econstructor; eauto).
  - constructor. now apply lup_app.
  - constructor. rewrite map_app. eauto.
  - econstructor; eauto. now apply has_kind_weak.
Qed.



(** ** Judgement renaming lemmas **)

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



(** ** Judgement substitution lemmas **)

Lemma has_kind_subst Delta Delta' t k sigma :
  has_kind Delta t k
  -> (forall x k', lup Delta x = Some k' -> has_kind Delta' (sigma x) k')
  -> has_kind Delta' t[sigma] k.
Proof.
  induction 1 in Delta', sigma |- *; cbn; intros HD.
  - now apply HD.
  - apply hk_app with k; intuition.
  - apply hk_abs. apply IHhas_kind. intros []; cbn.
    + intros k' [=]; subst. now constructor.
    + intros k' Hk. apply HD in Hk. eapply has_kind_ren; eauto.
  - apply hk_arrow; intuition.
  - apply hk_pi. apply IHhas_kind. intros []; cbn.
    + intros k' [=]; subst. now constructor.
    + intros k' Hk. apply HD in Hk. eapply has_kind_ren; eauto.
  - apply hk_comp. now apply IHhas_kind.
Qed.

Lemma has_type_subst Delta Delta' Gamma Gamma' e t sig1 sig2 :
  has_type Delta Gamma e t
  -> (forall n k, lup Delta n = Some k -> has_kind Delta' (sig1 n) k)
  -> (forall n t, lup Gamma n = Some t -> has_type Delta' Gamma' (sig2 n) t[sig1])
  -> has_type Delta' Gamma' (subst_prog sig1 sig2 e) t[sig1].
Proof.
  induction 1 in Delta', Gamma', sig1, sig2 |-*; cbn in *; intros H1 H2.
  - now apply H2.
  - constructor 2. apply IHhas_type.
    + intros [] k'; cbn.
      * intros [=]; subst. now constructor.
      * intros H'. apply H1 in H'. eapply has_kind_ren; eauto.
    + intros n t' H'. apply lup_map_el in H' as [t0[Ht ->]].
      apply H2 in Ht. asimpl. rewrite <- substRen_type.
      eapply has_type_ren; try apply Ht; trivial.
      intros. now apply map_nth_error.
  - constructor 3. erewrite ext_prog. apply (IHhas_type _ _ sig1 (up_prog_prog sig2)); trivial.
    + intros [] t; cbn.
      * intros [=]; subst. now constructor.
      * intros H'. apply H2 in H'. setoid_rewrite <- rinstId'_type at 3.
        eapply has_type_ren; try apply H'; cbn; trivial.
        setoid_rewrite rinstId'_type. trivial.
    + unfold up_prog_type. intros n. apply rinstId'_type.
    + reflexivity.
  - constructor 4. apply IHhas_type; trivial.
  - econstructor 5.
    + eapply IHhas_type1; trivial.
    + erewrite ext_prog. apply (IHhas_type2 _ _ sig1 (up_prog_prog sig2)); trivial.
      * intros [] t; cbn.
        -- intros [=]; subst. now constructor.
        -- intros H'. apply H2 in H'. setoid_rewrite <- rinstId'_type at 3.
           eapply has_type_ren; try apply H'; cbn; trivial.
           setoid_rewrite rinstId'_type. trivial.
      * unfold up_prog_type. intros n. apply rinstId'_type.
      * reflexivity.
  - replace (t1[t2..][sig1]) with (t1[up_type_type sig1][t2[sig1]..]) by now asimpl.
    econstructor 6. apply IHhas_type; trivial.
    eapply has_kind_subst; try apply H0. assumption.
  - econstructor 7.
    + eapply IHhas_type1; trivial.
    + eapply IHhas_type2; trivial.
  - econstructor 8.
    + apply conv_type_subst, H.
    + now apply IHhas_type.
Qed.

Lemma has_type_subst' Delta Gamma Gamma' e t sigma :
  has_type Delta Gamma e t
  -> (forall n t, lup Gamma n = Some t -> has_type Delta Gamma' (sigma n) t)
  -> has_type Delta Gamma' (subst_prog var_type sigma e) t.
Proof.
  intros. setoid_rewrite <- instId'_type. eapply has_type_subst; try apply H.
  - intros. now constructor.
  - setoid_rewrite instId'_type. assumption.
Qed.



(** ** Church-Rosser property **)

Inductive treds_type : type -> type -> Prop :=
| ct_tred t t' : tred_type t t' -> treds_type t t'
| ct_refl t : treds_type t t
| ct_trans t t' t'' : tred_type t t' -> treds_type t' t'' -> treds_type t t''.

Lemma treds_type_trans t1 t2 t3 :
  treds_type t1 t2 -> treds_type t2 t3 -> treds_type t1 t3.
Proof.
  induction 1 in t3 |- *.
  - now apply ct_trans.
  - tauto.
  - intros H' % IHtreds_type. eapply ct_trans; eauto.
Qed.

Inductive ptred : type -> type -> Prop :=
| pt_var x : ptred (var_type x) (var_type x)
| pt_beta k t1 t2 t1' t2' t : t = subst_type (t2'..) t1' -> ptred t1 t1' -> ptred t2 t2' -> ptred (app (abs k t1) t2) t
| pt_abs k t1 t2 : ptred t1 t2 -> ptred (abs k t1) (abs k t2)
| pt_app t1 t2 t1' t2' : ptred t1 t1' -> ptred t2 t2' -> ptred (app t1 t2) (app t1' t2')
| pt_arrow t1 t2 t1' t2' : ptred t1 t1' -> ptred t2 t2' -> ptred (arrow t1 t2) (arrow t1' t2')
| pt_pi t1 t2 k : ptred t1 t2 -> ptred (pi k t1) (pi k t2)
| pt_comp t1 t2 : ptred t1 t2 -> ptred (comp t1) (comp t2).

Inductive ptreds : type -> type -> Prop :=
| pt_ptred t t' : ptred t t' -> ptreds t t'
| pt_trans t t' t'' : ptred t t' -> ptreds t' t'' -> ptreds t t''.

Lemma treds_app1 t1 t2 t :
  treds_type t1 t2 -> treds_type (app t1 t) (app t2 t).
Proof.
  induction 1.
  - constructor. now apply ct_app1.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_app1.
Qed.

Lemma treds_app2 t1 t2 t :
  treds_type t1 t2 -> treds_type (app t t1) (app t t2).
Proof.
  induction 1.
  - constructor. now apply ct_app2.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_app2.
Qed.

Lemma treds_arrow1 t1 t2 t :
  treds_type t1 t2 -> treds_type (arrow t1 t) (arrow t2 t).
Proof.
  induction 1.
  - constructor. now apply ct_arrow1.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_arrow1.
Qed.

Lemma treds_arrow2 t1 t2 t :
  treds_type t1 t2 -> treds_type (arrow t t1) (arrow t t2).
Proof.
  induction 1.
  - constructor. now apply ct_arrow2.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_arrow2.
Qed.

Lemma treds_abs t1 t2 k :
  treds_type t1 t2 -> treds_type (abs k t1) (abs k t2).
Proof.
  induction 1.
  - constructor. now apply ct_abs.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_abs.
Qed.

Lemma treds_pi t1 t2 k :
  treds_type t1 t2 -> treds_type (pi k t1) (pi k t2).
Proof.
  induction 1.
  - constructor. now apply ct_pi.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_pi.
Qed.

Lemma treds_comp t1 t2 :
  treds_type t1 t2 -> treds_type (comp t1) (comp t2).
Proof.
  induction 1.
  - constructor. now apply ct_comp.
  - constructor 2.
  - econstructor 3; eauto. now apply ct_comp.
Qed.

Lemma ptred_treds t t' :
  ptred t t' -> treds_type t t'.
Proof.
  induction 1.
  - constructor 2.
  - eapply treds_type_trans. 2: constructor; apply ct_beta; eauto.
    eapply treds_type_trans.
    + apply treds_app1, treds_abs, IHptred1.
    + apply treds_app2, IHptred2.
  - now apply treds_abs.
  - eapply treds_type_trans.
    + apply treds_app1. eauto.
    + eapply treds_app2. eauto.
  - eapply treds_type_trans.
    + apply treds_arrow1. eauto.
    + eapply treds_arrow2. eauto.
  - now apply treds_pi.
  - now apply treds_comp.
Qed.

Lemma ptreds_treds t t' :
  ptreds t t' -> treds_type t t'.
Proof.
  induction 1.
  - now apply ptred_treds.
  - eapply treds_type_trans; eauto. now apply ptred_treds.
Qed.

Lemma ptred_refl t :
  ptred t t.
Proof.
  induction t; now constructor.
Qed.

Lemma tred_ptred t t' :
  tred_type t t' -> ptred t t'.
Proof.
  induction 1; econstructor; eauto; apply ptred_refl.
Qed.

Lemma treds_ptreds t t' :
  treds_type t t' -> ptreds t t'.
Proof.
  induction 1.
  - constructor 1. now apply tred_ptred.
  - constructor 1. apply ptred_refl.
  - econstructor 2; eauto. now apply tred_ptred.
Qed.

Fixpoint maxred t :=
  match t with
  | var_type x => var_type x
  | app (abs k t) t' => subst_type ((maxred t')..) (maxred t)
  | app t t' => app (maxred t) (maxred t')
  | abs k t => abs k (maxred t)
  | arrow t t' => arrow (maxred t) (maxred t')
  | pi k t => pi k (maxred t)
  | comp t => comp (maxred t)
  end.

Lemma ptred_ren t1 t1' xi :
  ptred t1 t1' -> ptred t1⟨xi⟩ t1'⟨xi⟩.
Proof.
  induction 1 in xi |- *; cbn; try now (constructor; eauto).
  subst. econstructor; eauto. now asimpl.
Qed.

Lemma ptred_subst t1 t1' sig sig' :
  ptred t1 t1' -> (forall n, ptred (sig n) (sig' n)) -> ptred t1[sig] t1'[sig'].
Proof.
  induction 1 in sig, sig' |- *; cbn; intros H'; try now (constructor; eauto).
  - apply H'.
  - subst. econstructor; eauto. 2: apply (IHptred1 _ (up_type_type sig')).
    + now asimpl.
    + intros []; cbn; try constructor. apply ptred_ren, H'.
  - constructor. apply IHptred. intros []; cbn; try constructor. apply ptred_ren, H'.
  - constructor. apply IHptred. intros []; cbn; try constructor. apply ptred_ren, H'.
Qed.

Lemma ptred_subst' t1 t1' t2 t2' :
  ptred t1 t1' -> ptred t2 t2' -> ptred t1[t2..] t1'[t2'..].
Proof.
  intros H1 H2. apply ptred_subst; trivial.
  intros []; cbn; trivial. constructor.
Qed.

Lemma maxred_ptred t t' :
  ptred t t' -> ptred t' (maxred t).
Proof.
  induction t in t' |- *; inversion 1; subst; cbn.
  - constructor.
  - apply ptred_subst'; eauto.
    specialize (IHt1 (abs k t1') (pt_abs _ H3)).
    cbn in IHt1. inversion IHt1; subst. apply H1.
  - destruct t1; cbn.
    + inversion H2; subst. constructor; eauto.
    + inversion H2; subst; constructor; eauto.
    + inversion H2; subst. eapply pt_beta; eauto.
      specialize (IHt1 (abs n t3) (pt_abs _ H5)).
    cbn in IHt1. inversion IHt1; subst. apply H1.
    + inversion H2; subst. constructor; eauto.
    + inversion H2; subst. constructor; eauto.
    + inversion H2; subst. constructor; eauto.
  - constructor. eauto.
  - constructor; eauto.
  - constructor. eauto.
  - constructor. eauto.
Qed.

Lemma Diamond_ptred t t1 t2 :
  ptred t t1 -> ptred t t2 -> { t' | ptred t1 t' /\ ptred t2 t' }.
Proof.
  intros H1 H2. exists (maxred t). split; now apply maxred_ptred.
Qed.

Lemma Church_Rosser_ptreds' t t1 t2 :
  ptred t t1 -> ptreds t t2 -> exists t', ptreds t1 t' /\ ptred t2 t'.
Proof.
  intros H. induction 1 in t1, H |- *.
  - destruct (Diamond_ptred H H0) as (t0 & H1 & H2).
    exists t0. split; trivial. now constructor.
  - destruct (Diamond_ptred H H0) as (t0 & H2 & H3).
    destruct (IHptreds t0 H3) as (t2 & H4 & H5).
    exists t2. split; trivial. econstructor 2; eauto.
Qed.

Lemma Church_Rosser_ptreds t t1 t2 :
  ptreds t t1 -> ptreds t t2 -> exists t', ptreds t1 t' /\ ptreds t2 t'.
Proof.
  induction 1 in t2 |-*; intros H1.
  - destruct (Church_Rosser_ptreds' H H1) as (t1 & H2 & H3).
    exists t1. split; trivial. now constructor.
  - destruct (Church_Rosser_ptreds' H H1) as (t1 & H2 & H3).
    destruct (IHptreds t1 H2) as (t3 & H4 & H5).
    exists t3. split; trivial. econstructor 2; eauto.
Qed.

Lemma Church_Rosser t t1 t2 :
  treds_type t t1 -> treds_type t t2 -> exists t', treds_type t1 t' /\ treds_type t2 t'.
Proof.
  intros H1 % treds_ptreds H2 % treds_ptreds.
  destruct (Church_Rosser_ptreds H1 H2) as [t' H].
  exists t'. split; apply ptreds_treds, H.
Qed.

Lemma Church_Rosser' t1 t2 :
  conv_type t1 t2 -> exists t, treds_type t1 t /\ treds_type t2 t.
Proof.
  induction 1.
  - exists y. split; now constructor.
  - exists x. split; now constructor.
  - firstorder eauto.
  - destruct IHclos_refl_sym_trans1 as [t1 H1], IHclos_refl_sym_trans2 as [t2 H2].
    destruct (@Church_Rosser y t1 t2) as [t Ht]; intuition.
    exists t. split; eapply treds_type_trans; eauto.
Qed.



(** ** Subject reduction **)

Lemma conv_type_comp t t' :
  conv_type t t' -> conv_type (comp t) (comp t').
Proof.
  induction 1.
  - constructor 1. now constructor.
  - constructor 2.
  - now constructor 3.
  - econstructor 4; eauto.
Qed.

Lemma treds_conv t t' :
  treds_type t t' -> conv_type t t'.
Proof.
  induction 1.
  - now constructor 1.
  - constructor 2.
  - econstructor 4; eauto. now constructor 1.
Qed.

Lemma treds_comp_inv' t1 t2' :
  treds_type (comp t1) t2' -> exists t2, t2' = comp t2.
Proof.
  remember (comp t1) as t1'.
  induction 1 in t1, Heqt1' |- *; subst.
  - inversion H; subst. now exists t2.
  - now exists t1.
  - inversion H; subst. eapply IHtreds_type. reflexivity.
Qed.

Lemma treds_comp_inv t1 t2 :
  treds_type (comp t1) (comp t2) -> treds_type t1 t2.
Proof.
  remember (comp t1) as t. remember (comp t2) as t'.
  induction 1 in t1, t2, Heqt, Heqt' |- *; subst.
  - constructor 1. inversion H; subst. apply H2.
  - injection Heqt'. intros ->. constructor 2.
  - inversion H; subst. eapply ct_trans; eauto.
Qed.

Lemma conv_comp_inv t1 t2 :
  conv_type (comp t1) (comp t2) -> conv_type t1 t2.
Proof.
  intros (t & H1 & H2) % Church_Rosser'.
  destruct (treds_comp_inv' H1) as [t1' ->].
  apply treds_comp_inv in H1, H2. econstructor 4.
  - apply treds_conv. apply H1.
  - constructor 3. now apply treds_conv.
Qed.

Lemma ht_ret_inv' Delta Gamma e t e' t' :
  has_type Delta Gamma e' t' -> e' = ret e -> conv_type t' (comp t) -> has_type Delta Gamma e t.
Proof.
  induction 1 in e, t |- *; try discriminate.
  - intros [=] H' % conv_comp_inv; subst. eapply ht_conv; eauto.
  - intros H1 H2. apply IHhas_type; trivial. econstructor 4; eauto.
Qed.

Lemma ht_ret_inv Delta Gamma e t :
  has_type Delta Gamma (ret e) (comp t) -> has_type Delta Gamma e t.
Proof.
  intros H. eapply ht_ret_inv'; eauto. constructor 2.
Qed.

Lemma treds_pi_inv' t1 t2' k :
  treds_type (pi k t1) t2' -> exists t2, t2' = pi k t2.
Proof.
  remember (pi k t1) as t1'.
  induction 1 in t1, Heqt1' |- *; subst.
  - inversion H; subst. now exists t2.
  - now exists t1.
  - inversion H; subst. eapply IHtreds_type. reflexivity.
Qed.

Lemma treds_pi_inv t1 t2 k k' :
  treds_type (pi k t1) (pi k' t2) -> treds_type t1 t2 /\ k = k'.
Proof.
  remember (pi k t1) as t. remember (pi k' t2) as t'.
  induction 1 in t1, t2, Heqt, Heqt' |- *; subst.
  - inversion H; subst. split; trivial. constructor 1. apply H1.
  - injection Heqt'. intros -> ->. split; trivial. constructor 2.
  - inversion H; subst. split.
    + eapply ct_trans; eauto. now apply IHtreds_type.
    + now apply (IHtreds_type t3 t2).
Qed.

Lemma conv_pi_inv k k' t t' :
  conv_type (pi k t) (pi k' t') -> conv_type t t' /\ k = k'.
Proof.
  intros (t'' & H1 & H2) % Church_Rosser'.
  destruct (treds_pi_inv' H1) as [t1' ->].
  apply treds_pi_inv in H1, H2 as [H2 ->]. split; trivial. econstructor 4.
  - apply treds_conv. apply H1.
  - constructor 3. now apply treds_conv.
Qed.

Lemma ht_tyabs_inv' Delta Gamma e t k k' e' t' :
  has_type Delta Gamma e' t' -> e' = tyabs k e -> conv_type t' (pi k' t)
    -> has_type (k :: Delta) (list_map (ren_type ↑) Gamma) e t /\ k = k'.
Proof.
  induction 1 in e, t |- *; try discriminate.
  - intros [=] H'; subst. apply conv_pi_inv in H' as [H' ->]. split; trivial. eapply ht_conv; eauto.
  - intros H1 H2. apply IHhas_type; trivial. econstructor 4; eauto.
Qed.

Lemma ht_tyabs_inv Delta Gamma e t k k' :
  has_type Delta Gamma (tyabs k e) (pi k' t)
    -> has_type (k :: Delta) (list_map (ren_type ↑) Gamma) e t /\ k = k'.
Proof.
  intros H. eapply ht_tyabs_inv'; eauto. constructor 2.
Qed.

Lemma treds_arrow_inv' t1 t2 t' :
  treds_type (arrow t1 (comp t2)) t' -> exists t1' t2', t' = arrow t1' (comp t2').
Proof.
  remember (arrow t1 (comp t2)) as t.
  induction 1 in t1, t2, Heqt |- *; subst.
  - inversion H; subst.
    + now exists t3, t2.
    + inversion H3; subst. now exists t1, t4.
  - now exists t1, t2.
  - inversion H; subst.
    + eapply IHtreds_type. reflexivity.
    + inversion H4; subst. eapply IHtreds_type. reflexivity.
Qed.

Lemma treds_arrow_inv t1 t2 t1' t2' :
  treds_type (arrow t1 (comp t2)) (arrow t1' (comp t2')) -> treds_type t1 t1' /\ treds_type t2 t2'.
Proof.
  remember (arrow t1 (comp t2)) as t. remember (arrow t1' (comp t2')) as t'.
  induction 1 in t1, t2, Heqt, Heqt' |- *; subst.
  - inversion H; subst.
    + split; try constructor 2. now constructor 1.
    + split; try constructor 2. inversion H1; subst. now constructor 1.
  - injection Heqt'. intros -> ->. split; constructor 2.
  - inversion H; subst; split.
    + eapply ct_trans; eauto. now apply (IHtreds_type t3 t2).
    + now apply (IHtreds_type t3 t2).
    + inversion H4; subst. now apply (IHtreds_type t1 t4).
    + inversion H4; subst. eapply ct_trans; eauto. now apply (IHtreds_type t1 t4).
Qed.

Lemma conv_arrow_inv t1 t2 t1' t2' :
  conv_type (arrow t1 (comp t2)) (arrow t1' (comp t2')) -> conv_type t1 t1' /\ conv_type t2 t2'.
Proof.
  intros (t'' & H1 & H2) % Church_Rosser'.
  destruct (treds_arrow_inv' H1) as [t [t' ->]].
  apply treds_arrow_inv in H1 as [H1 H1'], H2 as [H2 H2']. split; econstructor 4.
  - apply treds_conv. apply H1.
  - constructor 3. now apply treds_conv.
  - apply treds_conv. apply H1'.
  - constructor 3. now apply treds_conv.
Qed.

Lemma ht_tmabs_inv' Delta Gamma e t t1 t2 e' t' :
  has_type Delta Gamma e' t' -> e' = tmabs t e -> conv_type t' (arrow t1 (comp t2))
    -> has_type Delta (t :: Gamma) e (comp t2) /\ conv_type t t1.
Proof.
  induction 1 in e, t |- *; try discriminate.
  - intros [=] H'; subst. apply conv_arrow_inv in H' as [H1 H2].
    split; trivial. eapply ht_conv; eauto. now apply conv_type_comp.
  - intros H1 H2. apply IHhas_type; trivial. econstructor 4; eauto.
Qed.

Lemma ht_tmabs_inv Delta Gamma e t t1 t2 :
  has_type Delta Gamma (tmabs t e) (arrow t1 (comp t2))
    -> has_type Delta (t :: Gamma) e (comp t2) /\ conv_type t t1.
Proof.
  intros H. eapply ht_tmabs_inv'; eauto. constructor 2. 
Qed.

Lemma red_has_type Delta Gamma e e' t :
  has_type Delta Gamma e t -> red_prog e e' -> has_type Delta Gamma e' t.
Proof.
  induction 1 in e' |- *. 1-7: inversion 1; subst.
  - eapply has_type_subst'; eauto. intros []; cbn.
    + intros t [=]; subst. now apply ht_ret_inv in H.
    + intros t. apply ht_var.
  - apply ht_tyabs_inv in H as [H <-]. eapply has_type_subst; eauto.
    + intros []; cbn. intros k' [=]; subst; trivial. intros k'. apply hk_var.
    + intros n t (t' & Ht & ->) % lup_map_el. asimpl. now constructor.
  - apply ht_tmabs_inv in H as [H H']. eapply has_type_subst'; eauto.
    intros []; cbn. intros t' [=]; subst.
    + eapply ht_conv; eauto. now constructor 3.
    + intros k'. apply ht_var.
  - intros H' % IHhas_type. eapply ht_conv; eauto.
Qed.



(** ** EffHOL deduction system **)

Definition swap := 0 .: (↑ >> ↑).

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
| HOPL_ME phi e1 e2 : HOPL_prv A (after e1 (after e2 (ren_spec id swap id phi)))
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