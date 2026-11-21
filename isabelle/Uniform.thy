theory Uniform
  imports Sig_Confluence Reduction
begin

section \<open>Normalization notions and uniform normalization\<close>

text \<open>
  A normal form is clash-free if it is a fireball.  \<open>CFN M\<close>: some reduction from \<open>M\<close>
  reaches a clash-free normal form.  \<open>CFSN M\<close>: every reduction from \<open>M\<close> terminates and
  every normal form reachable from \<open>M\<close> is clash-free.
\<close>

definition CFN :: "trm \<Rightarrow> bool" where
  "CFN M \<longleftrightarrow> (\<exists>N. M \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N \<and> fb N)"

definition CFSN :: "trm \<Rightarrow> bool" where
  "CFSN M \<longleftrightarrow> SN_at cbv M \<and> (\<forall>N. M \<rightarrow>\<^sub>v\<^sup>* N \<longrightarrow> NF N \<longrightarrow> fb N)"

lemma NF_iff: "NF M \<longleftrightarrow> sig_normal M \<and> normal beta M"
  by (auto simp: normal_def cbv_def)

lemma fb_NF: "fb M \<Longrightarrow> sig_normal M \<Longrightarrow> NF M"
  using fb_no_beta[of M] by (auto simp: normal_def cbv_def)

lemma NF_imp_sig_normal: "NF M \<Longrightarrow> sig_normal M"
  by (simp add: NF_iff)

subsection \<open>\<open>\<sigma>\<close>-steps commute with the \<open>\<beta>\<^sub>v\<close>-step\<close>

lemma ss1: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> sig\<^sup>*\<^sup>* M N" by (rule r_into_rtranclp)

lemma Lam_sig_inv: "Lam x B \<rightarrow>\<^sub>\<sigma> P \<Longrightarrow> \<exists>B'. P = Lam x B' \<and> B \<rightarrow>\<^sub>\<sigma> B'"
  by (auto elim: sig.cases)

lemma Clo_sig_inv:
  assumes "Comp (Lam x B) K \<rightarrow>\<^sub>\<sigma> P"
  shows "(\<exists>B'. P = Comp (Lam x B') K \<and> B \<rightarrow>\<^sub>\<sigma> B') \<or> (\<exists>K'. P = Comp (Lam x B) K' \<and> K \<rightarrow>\<^sub>\<sigma> K') \<or>
     (K = Id \<and> P = Lam x B)"
  using assms
proof (cases rule: sig.cases)
  case (CompL B0)
  then show ?thesis using Lam_sig_inv by blast
qed auto

text \<open>A \<open>\<sigma>\<close>-step never destroys the \<open>\<beta>\<^sub>v\<close>-redex: the strong form below.\<close>

lemma beta_sig_commute: "M \<rightarrow>\<^sub>\<beta> M2 \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> M1 \<Longrightarrow> \<exists>M3. M1 \<rightarrow>\<^sub>\<beta> M3 \<and> sig\<^sup>*\<^sup>* M2 M3"
proof (induction arbitrary: M1 rule: beta.induct)
  case (Beta1 N x B K)
  from Beta1.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL P)
    from Clo_sig_inv[OF AppL(2)] show ?thesis
    proof (elim disjE exE conjE)
      fix B' assume "P = Comp (Lam x B') K" "B \<rightarrow>\<^sub>\<sigma> B'"
      then show ?thesis using AppL Beta1.hyps
        by (auto intro!: beta.Beta1 ss1 sig.CompL)
    next
      fix K' assume "P = Comp (Lam x B) K'" "K \<rightarrow>\<^sub>\<sigma> K'"
      then show ?thesis using AppL Beta1.hyps
        by (auto intro!: beta.Beta1 ss1 sig.CompR sig.ExtnR)
    next
      assume "K = Id" "P = Lam x B"
      then show ?thesis using AppL Beta1.hyps
        by (auto intro!: beta.Beta2)
    qed
  next
    case (AppR N')
    have "fb N'" using sig_fb[OF Beta1.hyps AppR(2)] .
    then show ?thesis using AppR by (auto intro!: beta.Beta1 ss1 sig.CompR sig.ExtnL)
  next
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>\<beta> Comp B (Extn (Nm y) x K)" using AppConst by (simp add: beta.VarClos)
    then show ?thesis using AppConst by auto
  qed
next
  case (Beta2 N x B)
  from Beta2.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL P)
    then obtain B' where "P = Lam x B'" "B \<rightarrow>\<^sub>\<sigma> B'" using Lam_sig_inv by blast
    then show ?thesis using AppL Beta2.hyps by (auto intro!: beta.Beta2 ss1 sig.CompL)
  next
    case (AppR N')
    have "fb N'" using sig_fb[OF Beta2.hyps AppR(2)] .
    then show ?thesis using AppR by (auto intro!: beta.Beta2 ss1 sig.CompR sig.ExtnL)
  next
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>\<beta> Comp B (Extn (Nm y) x Id)" using AppConst by (simp add: beta.VarLam)
    then show ?thesis using AppConst by auto
  qed
next
  case (AppL M M' L)
  from AppL.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL M1a)
    from AppL.IH[OF AppL(2)] obtain M3 where "M1a \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
    then show ?thesis using AppL(1)
      by (auto intro!: beta.AppL sig_steps_lift[of "\<lambda>P. App P L"] sig.AppL)
  next
    case (AppR L')
    then show ?thesis using AppL.hyps by (auto intro!: beta.AppL ss1 sig.AppR)
  next
    case (AppConst y)
    have "M1 \<rightarrow>\<^sub>\<beta> Comp (Var y) M'" using AppConst AppL.hyps by (simp add: beta.VarR)
    moreover have "sig\<^sup>*\<^sup>* (App M' L) (Comp (Var y) M')" using AppConst by (auto intro: ss1 sig.AppConst)
    ultimately show ?thesis by blast
  qed
next
  case (AppR L M M')
  from AppR.prems show ?case
  proof (cases rule: sig.cases)
    case (AppL L')
    have "fb L'" using sig_fb[OF AppR.hyps(1) AppL(2)] .
    then show ?thesis using AppL AppR.hyps by (auto intro!: beta.AppR ss1 sig.AppL)
  next
    case (AppR M1a)
    from AppR.IH[OF AppR(2)] obtain M3 where "M1a \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
    then show ?thesis using AppR(1) AppR.hyps(1)
      by (auto intro!: beta.AppR sig_steps_lift[of "\<lambda>P. App L P"] sig.AppR)
  next
    case (AppConst y)
    then show ?thesis using AppR.hyps(2) Nm_no_beta by blast
  qed
next
  case (VarClos x y B K)
  from VarClos.prems show ?case
  proof (cases rule: sig.cases)
    case (CompR P)
    from Clo_sig_inv[OF CompR(2)] show ?thesis
    proof (elim disjE exE conjE)
      fix B' assume "P = Comp (Lam y B') K" "B \<rightarrow>\<^sub>\<sigma> B'"
      then show ?thesis using CompR by (auto intro!: beta.VarClos ss1 sig.CompL)
    next
      fix K' assume "P = Comp (Lam y B) K'" "K \<rightarrow>\<^sub>\<sigma> K'"
      then show ?thesis using CompR by (auto intro!: beta.VarClos ss1 sig.CompR sig.ExtnR)
    next
      assume "K = Id" "P = Lam y B"
      then show ?thesis using CompR by (auto intro!: beta.VarLam)
    qed
  qed (auto elim: sig.cases)
next
  case (VarLam x y B)
  from VarLam.prems show ?case
  proof (cases rule: sig.cases)
    case (CompR P)
    then obtain B' where "P = Lam y B'" "B \<rightarrow>\<^sub>\<sigma> B'" using Lam_sig_inv by blast
    then show ?thesis using CompR by (auto intro!: beta.VarLam ss1 sig.CompL)
  qed (auto elim: sig.cases)
next
  case (VarR M M' x)
  from VarR.prems show ?case
  proof (cases rule: sig.cases)
    case (CompR M1a)
    from VarR.IH[OF CompR(2)] obtain M3 where "M1a \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
    then show ?thesis using CompR(1)
      by (auto intro!: beta.VarR sig_steps_lift[of "\<lambda>P. Comp (Var x) P"] sig.CompR)
  qed (use VarR.hyps in \<open>auto dest: Id_no_beta Extn_no_beta Var_no_beta Nm_no_beta elim: sig.cases\<close>)
qed

subsection \<open>\<open>\<sigma>\<close>-normal forms\<close>

lemma sig_nf: "\<exists>N. sig\<^sup>*\<^sup>* M N \<and> sig_normal N"
proof -
  have "SN_at sig M" by (rule sig_SN)
  then show ?thesis
  proof (induction rule: SN_at_induct)
    case (step a)
    show ?case
    proof (cases "sig_normal a")
      case True then show ?thesis by blast
    next
      case False
      then obtain b where "a \<rightarrow>\<^sub>\<sigma> b" by (auto simp: normal_def)
      with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
    qed
  qed
qed

lemma sig_steps_tlength: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> tlength N \<le> tlength M"
  by (induction rule: rtranclp_induct) (auto dest: sig_tlength_decrease)

definition snf :: "trm \<Rightarrow> trm" where
  "snf M = (SOME N. sig\<^sup>*\<^sup>* M N \<and> sig_normal N)"

lemma snf_spec: "sig\<^sup>*\<^sup>* M (snf M) \<and> sig_normal (snf M)"
  unfolding snf_def using sig_nf by (rule someI_ex)

lemma snf_unique: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig_normal N \<Longrightarrow> snf M = N"
proof -
  assume r: "sig\<^sup>*\<^sup>* M N" and n: "sig_normal N"
  obtain P where p1: "sig\<^sup>*\<^sup>* (snf M) P" and p2: "sig\<^sup>*\<^sup>* N P"
    using sig_confluent[OF snf_spec[THEN conjunct1] r] by blast
  have "P = snf M" using normal_rtranclp[OF snf_spec[THEN conjunct2] p1] .
  moreover have "P = N" using normal_rtranclp[OF n p2] .
  ultimately show ?thesis by simp
qed

lemma snf_steps: "sig\<^sup>*\<^sup>* M M' \<Longrightarrow> snf M' = snf M"
proof -
  assume r: "sig\<^sup>*\<^sup>* M M'"
  have "sig\<^sup>*\<^sup>* M (snf M')" using r snf_spec[of M'] by (meson rtranclp_trans)
  then have "snf M = snf M'" using snf_unique snf_spec by blast
  then show ?thesis by simp
qed

lemma snf_beta:
  "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> \<exists>M3. snf M \<rightarrow>\<^sub>\<beta> M3 \<and> sig\<^sup>*\<^sup>* M' M3"
proof (induction "tlength M" arbitrary: M M' rule: less_induct)
  case less
  show ?case
  proof (cases "sig_normal M")
    case True
    then have "snf M = M" using snf_unique by blast
    then show ?thesis using less.prems by auto
  next
    case False
    then obtain M1 where s: "M \<rightarrow>\<^sub>\<sigma> M1" by (auto simp: normal_def)
    from beta_sig_commute[OF less.prems s] obtain M3' where
      a: "M1 \<rightarrow>\<^sub>\<beta> M3'" "sig\<^sup>*\<^sup>* M' M3'" by blast
    have lt: "tlength M1 < tlength M" using sig_tlength_decrease[OF s] .
    from less.hyps[OF lt a(1)] obtain M3 where b: "snf M1 \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M3' M3"
      by blast
    have "snf M1 = snf M" using snf_steps[OF ss1[OF s]] .
    then show ?thesis using b a(2) by (metis rtranclp_trans)
  qed
qed

subsection \<open>The deterministic chain\<close>

inductive cd :: "trm \<Rightarrow> nat \<Rightarrow> trm \<Rightarrow> bool" where
  cd0: "normal beta (snf M) \<Longrightarrow> cd M 0 (snf M)"
| cdS: "snf M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> cd N n E \<Longrightarrow> cd M (Suc n) E"

lemma cd_snf: "cd A n E \<Longrightarrow> snf A = snf B \<Longrightarrow> cd B n E"
proof (cases rule: cd.cases)
  assume "cd A n E" "snf A = snf B"
  {
    assume "normal beta (snf A)" "n = 0" "E = snf A"
    then show ?thesis using \<open>snf A = snf B\<close> by (metis cd0)
  }
  {
    fix N m assume "n = Suc m" "snf A \<rightarrow>\<^sub>\<beta> N" "cd N m E"
    then show ?thesis using \<open>snf A = snf B\<close> by (metis cdS)
  }
qed

lemma cd_det: "cd M n E \<Longrightarrow> cd M n' E' \<Longrightarrow> n = n' \<and> E = E'"
proof (induction arbitrary: n' E' rule: cd.induct)
  case (cd0 M)
  from cd0.prems show ?case
    by (cases rule: cd.cases) (use cd0.hyps in \<open>auto simp: normal_def\<close>)
next
  case (cdS M N n E)
  note h = cdS.hyps(1) and IH = cdS.IH
  from cdS.prems show ?case
  proof (cases rule: cd.cases)
    case cd0
    then show ?thesis using h by (auto simp: normal_def)
  next
    case (cdS N' m)
    then have "N' = N" using beta_det h by blast
    then show ?thesis using IH cdS by blast
  qed
qed

lemma cd_back_sig: "M \<rightarrow>\<^sub>\<sigma> M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M n E"
  using cd_snf snf_steps[OF ss1] by metis

lemma cd_fwd_sig: "M \<rightarrow>\<^sub>\<sigma> M' \<Longrightarrow> cd M n E \<Longrightarrow> cd M' n E"
  using cd_snf snf_steps[OF ss1] by metis

lemma cd_back_beta: "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> cd M' n E \<Longrightarrow> cd M (Suc n) E"
proof -
  assume b: "M \<rightarrow>\<^sub>\<beta> M'" and c: "cd M' n E"
  from snf_beta[OF b] obtain M3 where m3: "snf M \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
  have "cd M3 n E" using cd_snf[OF c] snf_steps[OF m3(2)] by simp
  then show ?thesis by (rule cdS[OF m3(1)])
qed

lemma cd_fwd_beta: "M \<rightarrow>\<^sub>\<beta> M' \<Longrightarrow> cd M n E \<Longrightarrow> \<exists>m. n = Suc m \<and> cd M' m E"
proof -
  assume b: "M \<rightarrow>\<^sub>\<beta> M'" and c: "cd M n E"
  from snf_beta[OF b] obtain M3 where m3: "snf M \<rightarrow>\<^sub>\<beta> M3" "sig\<^sup>*\<^sup>* M' M3" by blast
  from c show ?thesis
  proof (cases rule: cd.cases)
    case cd0
    then show ?thesis using m3(1) by (auto simp: normal_def)
  next
    case (cdS N m)
    then have "N = M3" using beta_det m3(1) by blast
    then have "cd M3 m E" using cdS by simp
    then have "cd M' m E" using cd_snf snf_steps[OF m3(2)] by metis
    then show ?thesis using cdS by blast
  qed
qed

lemma NF_cd: "NF N \<Longrightarrow> cd N 0 N"
proof -
  assume n: "NF N"
  have sn: "snf N = N" using snf_unique[OF rtranclp.rtrancl_refl NF_imp_sig_normal[OF n]] .
  have "normal beta N" using n by (simp add: NF_iff)
  then show ?thesis using cd0[of N] sn by simp
qed

lemma steps_cd: "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> NF N \<Longrightarrow> \<exists>k. cd M k N"
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case using NF_cd by blast
next
  case (step M M')
  then obtain k where c: "cd M' k N" by blast
  from step.hyps(1) consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: cbv_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_back_sig c by blast
  next
    case 2 then show ?thesis using cd_back_beta c by blast
  qed
qed

lemma cd_SN: "cd M n E \<Longrightarrow> SN_at cbv M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. cd M n E \<Longrightarrow> SN_at cbv M"
  proof -
    fix M
    show "cd M n E \<Longrightarrow> SN_at cbv M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>v N"
        then consider "M \<rightarrow>\<^sub>\<sigma> N" | "M \<rightarrow>\<^sub>\<beta> N" by (auto simp: cbv_def)
        then show "SN_at cbv N"
        proof cases
          case 1
          have "cd N n E" using cd_fwd_sig[OF 1 less.prems] .
          moreover have "tlength N < tlength M" using sig_tlength_decrease[OF 1] .
          ultimately show ?thesis using less.hyps by blast
        next
          case 2
          then obtain m where "n = Suc m" "cd N m E" using cd_fwd_beta less.prems by blast
          then show ?thesis using IHn by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma cd_reach_end: "M \<rightarrow>\<^sub>v\<^sup>* N' \<Longrightarrow> cd M n E \<Longrightarrow> NF N' \<Longrightarrow> N' = E"
proof (induction arbitrary: n rule: converse_rtranclp_induct)
  case base
  then show ?case using NF_cd cd_det by blast
next
  case (step M M')
  from step.hyps(1) consider "M \<rightarrow>\<^sub>\<sigma> M'" | "M \<rightarrow>\<^sub>\<beta> M'" by (auto simp: cbv_def)
  then show ?case
  proof cases
    case 1 then show ?thesis using cd_fwd_sig step.prems step.IH by blast
  next
    case 2 then show ?thesis using cd_fwd_beta step.prems step.IH by blast
  qed
qed

subsection \<open>Main results of this section\<close>

theorem NF_unique: "M \<rightarrow>\<^sub>v\<^sup>* N1 \<Longrightarrow> NF N1 \<Longrightarrow> M \<rightarrow>\<^sub>v\<^sup>* N2 \<Longrightarrow> NF N2 \<Longrightarrow> N1 = N2"
proof -
  assume r1: "M \<rightarrow>\<^sub>v\<^sup>* N1" and n1: "NF N1" and r2: "M \<rightarrow>\<^sub>v\<^sup>* N2" and n2: "NF N2"
  from steps_cd[OF r1 n1] obtain k where "cd M k N1" by blast
  then show ?thesis using cd_reach_end[OF r2 _ n2] by metis
qed

theorem WN_imp_SN: "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> NF N \<Longrightarrow> SN_at cbv M"
  using steps_cd cd_SN by blast

theorem CFN_imp_CFSN: "CFN M \<Longrightarrow> CFSN M"
proof -
  assume "CFN M"
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" and c: "fb N"
    by (auto simp: CFN_def)
  have "SN_at cbv M" by (rule WN_imp_SN[OF r n])
  moreover have "fb N'" if "M \<rightarrow>\<^sub>v\<^sup>* N'" "NF N'" for N'
    using NF_unique[OF r n that] c by simp
  ultimately show "CFSN M" by (auto simp: CFSN_def)
qed

lemma SN_normalizes: "SN_at cbv M \<Longrightarrow> \<exists>N. M \<rightarrow>\<^sub>v\<^sup>* N \<and> NF N"
proof (induction rule: SN_at_induct)
  case (step a)
  show ?case
  proof (cases "NF a")
    case True then show ?thesis by blast
  next
    case False
    then obtain b where "a \<rightarrow>\<^sub>v b" by (auto simp: normal_def)
    with step.IH[OF this] show ?thesis by (meson converse_rtranclp_into_rtranclp)
  qed
qed

theorem CFSN_imp_CFN: "CFSN M \<Longrightarrow> CFN M"
  unfolding CFSN_def CFN_def using SN_normalizes by blast

theorem CFN_iff_CFSN: "CFN M \<longleftrightarrow> CFSN M"
  using CFN_imp_CFSN CFSN_imp_CFN by blast

lemma CFN_back: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> CFN M' \<Longrightarrow> CFN M"
  unfolding CFN_def by (meson converse_rtranclp_into_rtranclp)

lemma CFN_back_steps: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> CFN M' \<Longrightarrow> CFN M"
  by (induction rule: converse_rtranclp_induct) (auto intro: CFN_back)

lemma CFN_fwd: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> CFN M \<Longrightarrow> CFN M'"
proof -
  assume s: "M \<rightarrow>\<^sub>v M'" and c: "CFN M"
  from c have "CFSN M" by (rule CFN_imp_CFSN)
  then have sn: "SN_at cbv M'" and cf: "\<forall>N. M \<rightarrow>\<^sub>v\<^sup>* N \<longrightarrow> NF N \<longrightarrow> fb N"
    using s by (auto simp: CFSN_def intro: SN_at_step)
  from SN_normalizes[OF sn] obtain N where r: "M' \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" by blast
  have "fb N" using cf r n s by (meson converse_rtranclp_into_rtranclp)
  then show "CFN M'" using r n by (auto simp: CFN_def)
qed

lemma CFN_fwd_steps: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> CFN M \<Longrightarrow> CFN M'"
  by (induction rule: rtranclp_induct) (auto intro: CFN_fwd)

subsection \<open>Forward closure for names\<close>

lemma NF_Nm: "NF (Nm x)"
  by (auto simp: normal_def cbv_def elim: sig.cases beta.cases)

lemma Nm_fwd: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> M \<rightarrow>\<^sub>v\<^sup>* Nm x \<Longrightarrow> M' \<rightarrow>\<^sub>v\<^sup>* Nm x"
proof -
  assume s: "M \<rightarrow>\<^sub>v M'" and r: "M \<rightarrow>\<^sub>v\<^sup>* Nm x"
  have "SN_at cbv M" using WN_imp_SN[OF r NF_Nm] .
  then have "SN_at cbv M'" using s by (rule SN_at_step)
  then obtain N where r': "M' \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" using SN_normalizes by blast
  have "M \<rightarrow>\<^sub>v\<^sup>* N" using s r' by (rule converse_rtranclp_into_rtranclp)
  then have "N = Nm x" using NF_unique[OF _ n r NF_Nm] by blast
  then show ?thesis using r' by simp
qed

end
