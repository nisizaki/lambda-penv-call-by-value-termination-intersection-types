theory Conservative
  imports Sorted Main_Results
begin

section \<open>Conservativity over call-by-value \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close> on sorted terms\<close>

text \<open>
  On sorted terms none of the new rules (AppConst, ConstComp, VarLam, VarClos) applies,
  sortedness is preserved, and the reduction of \<open>\<lambda>penv\<^sub>c\<^sub>b\<^sub>v\<close> coincides with that of
  call-by-value \<open>\<lambda>\<^sub>e\<^sub>n\<^sub>v\<close>.  Sorted normal forms are fireballs.
\<close>

lemma sig0_imp_sig: "sig0 M N \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N"
  by (induction rule: sig0.induct) (auto intro: sig.intros)

lemma sig_sorted_imp_sig0: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> tm M \<or> en M \<Longrightarrow> sig0 M N"
  by (induction rule: sig.induct) (auto intro: sig0.intros)

lemma sorted_sig_iff: "tm M \<or> en M \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<longleftrightarrow> sig0 M N"
  using sig0_imp_sig sig_sorted_imp_sig0 by blast

lemma beta0_imp_beta: "beta0 M N \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N"
  by (induction rule: beta0.induct) (auto intro: beta.intros)

lemma beta_sorted_imp_beta0: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> tm M \<or> en M \<Longrightarrow> beta0 M N"
  by (induction rule: beta.induct) (auto intro: beta0.intros)

lemma sorted_beta_iff: "tm M \<or> en M \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N \<longleftrightarrow> beta0 M N"
  using beta0_imp_beta beta_sorted_imp_beta0 by blast

lemma sorted_cbv_iff: "tm M \<or> en M \<Longrightarrow> M \<rightarrow>\<^sub>v N \<longleftrightarrow> cbv0 M N"
  by (simp add: cbv_def cbv0_def sorted_sig_iff sorted_beta_iff)

lemma sig0_sorted: "sig0 M N \<Longrightarrow> (tm M \<longrightarrow> tm N) \<and> (en M \<longrightarrow> en N)"
  by (induction rule: sig0.induct) auto

lemma beta0_sorted: "beta0 M N \<Longrightarrow> (tm M \<longrightarrow> tm N) \<and> (en M \<longrightarrow> en N)"
  by (induction rule: beta0.induct) auto

lemma cbv_sorted: "M \<rightarrow>\<^sub>v N \<Longrightarrow> (tm M \<longrightarrow> tm N) \<and> (en M \<longrightarrow> en N)"
proof -
  assume h: "M \<rightarrow>\<^sub>v N"
  show ?thesis
  proof (intro conjI impI)
    assume "tm M"
    then have "cbv0 M N" using h sorted_cbv_iff by blast
    then show "tm N" using sig0_sorted beta0_sorted \<open>tm M\<close> unfolding cbv0_def by blast
  next
    assume "en M"
    then have "cbv0 M N" using h sorted_cbv_iff by blast
    then show "en N" using sig0_sorted beta0_sorted \<open>en M\<close> unfolding cbv0_def by blast
  qed
qed

lemma cbv_steps_sorted: "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> tm M \<Longrightarrow> tm N"
  by (induction rule: rtranclp_induct) (auto dest: cbv_sorted)

lemma inert_not_en: "inert M \<Longrightarrow> \<not> en M"
  by (auto elim: inert.cases)

lemma NF_AppL: "NF (App M N) \<Longrightarrow> NF M"
  by (auto simp: normal_def dest: cbv_AppL)

lemma NF_AppR: "NF (App M N) \<Longrightarrow> fb M \<Longrightarrow> NF N"
  by (auto simp: normal_def cbv_def intro: sig.AppR beta.AppR)

lemma NF_CompR_Var: "NF (Comp (Var x) N) \<Longrightarrow> NF N"
  by (auto simp: normal_def dest: cbv_VarR)

lemma sorted_NF_fb': "(tm M \<longrightarrow> NF M \<longrightarrow> fb M) \<and> (en M \<longrightarrow> NF M \<longrightarrow> fb M)"
proof (induction M)
  case (Var x) then show ?case by simp
next
  case (Lam x M) then show ?case by (simp add: FLam)
next
  case Id then show ?case by (simp add: FId)
next
  case (Extn M1 x M2) then show ?case by (simp add: FExtn)
next
  case (Nm x) then show ?case by simp
next
  case (App M1 M2)
  have "fb (App M1 M2)" if t: "tm (App M1 M2)" and n: "NF (App M1 M2)"
  proof -
    have n1: "NF M1" using NF_AppL[OF n] .
    have f1: "fb M1" using App.IH(1) t n1 by simp
    have n2: "NF M2" using NF_AppR[OF n f1] .
    have f2: "fb M2" using App.IH(2) t n2 by simp
    from f1 show ?thesis
    proof (cases rule: fb_cases)
      case inert then show ?thesis using f2 by (simp add: fb_App_iff)
    next
      case (lam x B)
      then have "App M1 M2 \<rightarrow>\<^sub>v Comp B (Extn M2 x Id)" using f2 by (simp add: beta_imp_cbv beta.Beta2)
      then show ?thesis using n by (auto simp: normal_def)
    next
      case (clo x B L)
      then have "App M1 M2 \<rightarrow>\<^sub>v Comp B (Extn M2 x L)" using f2 by (simp add: beta_imp_cbv beta.Beta1)
      then show ?thesis using n by (auto simp: normal_def)
    qed (use t in auto)
  qed
  then show ?case by simp
next
  case (Comp M1 M2)
  have r: "\<not> Comp M1 M2 \<rightarrow>\<^sub>\<sigma> P" if "NF (Comp M1 M2)" for P
    using that by (auto simp: normal_def cbv_def)
  have e: "\<not> NF (Comp M1 M2)" if "en M1"
  proof
    assume n: "NF (Comp M1 M2)"
    show False
    proof (cases M1)
      case Id then show False using r[OF n] sig.IdL by blast
    next
      case (Extn P y Q) then show False using r[OF n] sig.DExtn by blast
    next
      case (Comp P Q) then show False using r[OF n] sig.Ass by blast
    qed (use that in auto)
  qed
  have "fb (Comp M1 M2)" if t: "tm (Comp M1 M2)" and n: "NF (Comp M1 M2)"
  proof (cases M1)
    case (Var x)
    have n2: "NF M2" using NF_CompR_Var n Var by simp
    have f2: "fb M2" using Comp.IH(2) t n2 by simp
    have en2: "en M2" using t by simp
    from f2 show ?thesis
    proof (cases rule: fb_cases)
      case inert then show ?thesis using en2 inert_not_en by blast
    next
      case id then show ?thesis using r[OF n] sig.IdR by blast
    next
      case (extn P y Q)
      show ?thesis
      proof (cases "y = x")
        case True then show ?thesis using r[OF n] sig.VarRef Var extn by blast
      next
        case False then show ?thesis using r[OF n] sig.VarSkip[OF False] Var extn by blast
      qed
    qed (use en2 in auto)
  next
    case (Lam x B) then show ?thesis by (simp add: FClo)
  next
    case (App P Q) then show ?thesis using r[OF n] sig.DApp by blast
  next
    case Id then show ?thesis using r[OF n] sig.IdL by blast
  next
    case (Extn P y Q) then show ?thesis using r[OF n] sig.DExtn by blast
  next
    case (Comp P Q) then show ?thesis using r[OF n] sig.Ass by blast
  next
    case (Nm x) then show ?thesis using t by simp
  qed
  moreover have "en (Comp M1 M2) \<Longrightarrow> NF (Comp M1 M2) \<Longrightarrow> fb (Comp M1 M2)" using e by simp
  ultimately show ?case by blast
qed

lemma sorted_NF_fb: "tm N \<Longrightarrow> NF N \<Longrightarrow> fb N"
  using sorted_NF_fb' by blast

theorem sorted_cbv_steps_iff: "tm M \<Longrightarrow> M \<rightarrow>\<^sub>v\<^sup>* N \<longleftrightarrow> cbv0\<^sup>*\<^sup>* M N"
proof
  assume tm: "tm M" and r: "M \<rightarrow>\<^sub>v\<^sup>* N"
  from r show "cbv0\<^sup>*\<^sup>* M N"
  proof (induction rule: rtranclp_induct)
    case base then show ?case by (rule rtranclp.rtrancl_refl)
  next
    case (step b c)
    have tb: "tm b" by (rule cbv_steps_sorted[OF step.hyps(1) tm])
    have "cbv0 b c" by (rule iffD1[OF sorted_cbv_iff[OF disjI1[OF tb]] step.hyps(2)])
    show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH \<open>cbv0 b c\<close>])
  qed
next
  assume tm: "tm M" and r: "cbv0\<^sup>*\<^sup>* M N"
  from r show "M \<rightarrow>\<^sub>v\<^sup>* N"
  proof (induction rule: rtranclp_induct)
    case base then show ?case by (rule rtranclp.rtrancl_refl)
  next
    case (step b c)
    have tb: "tm b" by (rule cbv_steps_sorted[OF step.IH tm])
    have "b \<rightarrow>\<^sub>v c" by (rule iffD2[OF sorted_cbv_iff[OF disjI1[OF tb]] step.hyps(2)])
    show ?case by (rule rtranclp.rtrancl_into_rtrancl[OF step.IH \<open>b \<rightarrow>\<^sub>v c\<close>])
  qed
qed

theorem conservative_CFN: "tm M \<Longrightarrow> CFN M \<longleftrightarrow> CFN0 M"
proof -
  assume tm: "tm M"
  have nf: "\<And>N. tm N \<Longrightarrow> NF N \<longleftrightarrow> normal cbv0 N"
    by (simp add: normal_def cbv_def cbv0_def sorted_sig_iff sorted_beta_iff)
  show ?thesis
  proof
    assume "CFN M"
    then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" and f: "fb N" unfolding CFN_def by blast
    have "tm N" using cbv_steps_sorted r tm by blast
    then have "normal cbv0 N" using nf n by blast
    with r f show "CFN0 M" unfolding CFN0_def using tm sorted_cbv_steps_iff by blast
  next
    assume "CFN0 M"
    then obtain N where r: "cbv0\<^sup>*\<^sup>* M N" and n: "normal cbv0 N" and f: "fb N" unfolding CFN0_def by blast
    have r': "M \<rightarrow>\<^sub>v\<^sup>* N" using r tm sorted_cbv_steps_iff by blast
    have tN: "tm N" using cbv_steps_sorted r' tm by blast
    have "NF N" using nf[OF tN] n by blast
    then show "CFN M" unfolding CFN_def using r' f by blast
  qed
qed

theorem conservative_Typ: "tm M \<Longrightarrow> Typ M \<longleftrightarrow> CFN0 M"
  using conservative_CFN main_characterization by blast

end
