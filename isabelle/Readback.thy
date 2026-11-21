theory Readback
  imports Conservative Lambda
begin

section \<open>Readback into the \<open>\<lambda>\<close>-calculus: conservativity over open call-by-value\<close>

text \<open>Adapted from the call-by-value \<open>\<lambda>env\<close> development.  \<open>tm\<close>, \<open>en\<close>, \<open>pure\<close> are in \<open>Sorted\<close>;
  preservation of sortedness and \<open>sorted_NF_fb\<close> are in \<open>Conservative\<close>.\<close>

definition junk :: dB where "junk = DAbs (DVar 0)"

lemma subst_junk [simp]: "junk[s/k] = junk"
  by (simp add: junk_def)

fun rb :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> dB" and rbe :: "trm \<Rightarrow> (var \<Rightarrow> dB) \<Rightarrow> (var \<Rightarrow> dB)" where
  "rb (Var x) \<rho> = \<rho> x"
| "rb (Lam x M) \<rho> = DAbs (rb M ((\<lambda>y. lift (\<rho> y) 0)(x := DVar 0)))"
| "rb (App M N) \<rho> = DApp (rb M \<rho>) (rb N \<rho>)"
| "rb (Comp M L) \<rho> = rb M (rbe L \<rho>)"
| "rb Id \<rho> = junk"
| "rb (Extn M x L) \<rho> = junk"
| "rb (Nm x) \<rho> = junk"
| "rbe (Var x) \<rho> = \<rho>"
| "rbe (Lam x M) \<rho> = \<rho>"
| "rbe (App M N) \<rho> = \<rho>"
| "rbe (Comp L1 L2) \<rho> = rbe L1 (rbe L2 \<rho>)"
| "rbe Id \<rho> = \<rho>"
| "rbe (Extn M x L) \<rho> = (rbe L \<rho>)(x := rb M \<rho>)"
| "rbe (Nm x) \<rho> = \<rho>"

lemma rb_subst:
  "(\<forall>\<sigma> s k. (rb M \<sigma>)[s/k] = rb M (\<lambda>y. (\<sigma> y)[s/k])) \<and>
   (\<forall>\<sigma> s k. rbe M (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe M \<sigma> y)[s/k]))"
proof (induction M)
  case (Var x)
  then show ?case by simp
next
  case (Lam x M)
  have "(rb (Lam x M) \<sigma>)[s/k] = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])" for \<sigma> s k
  proof -
    have fe: "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1])
            = (\<lambda>y. lift ((\<sigma> y)[s/k]) 0)(x := DVar 0)"
      by (rule ext) (simp add: lift_subst_lt)
    have "(rb (Lam x M) \<sigma>)[s/k]
        = DAbs ((rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[lift s 0 / k + 1])"
      by simp
    also have "\<dots> = DAbs (rb M (\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[lift s 0 / k + 1]))"
      using Lam.IH by simp
    also have "\<dots> = rb (Lam x M) (\<lambda>y. (\<sigma> y)[s/k])"
      by (simp only: fe rb.simps)
    finally show ?thesis .
  qed
  then show ?case by simp
next
  case (App M N)
  then show ?case by simp
next
  case Id
  then show ?case by simp
next
  case (Nm y)
  then show ?case by simp
next
  case (Extn M x L)
  have "rbe (Extn M x L) (\<lambda>y. (\<sigma> y)[s/k]) = (\<lambda>y. (rbe (Extn M x L) \<sigma> y)[s/k])" for \<sigma> s k
    using Extn.IH by (auto intro!: ext)
  then show ?case by simp
next
  case (Comp M L)
  then show ?case by simp
qed

lemma beta_rb:
  "(rb M ((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)))[t/0] = rb M (\<sigma>(x := t))"
proof -
  have "(\<lambda>y. (((\<lambda>y. lift (\<sigma> y) 0)(x := DVar 0)) y)[t/0]) = \<sigma>(x := t)"
    by (rule ext) simp
  then show ?thesis
    using rb_subst[of M] by simp
qed

subsection \<open>Simulation\<close>

lemma sig_sorted:
  "sig0 M N \<Longrightarrow>
     (tm M \<longrightarrow> tm N \<and> (\<forall>\<rho>. rb N \<rho> = rb M \<rho>)) \<and>
     (en M \<longrightarrow> en N \<and> (\<forall>\<rho>. rbe N \<rho> = rbe M \<rho>))"
  by (induction rule: sig0.induct) (auto simp: fun_upd_def)

lemma beta_not_en: "beta0 M N \<Longrightarrow> \<not> en M"
  by (induction rule: beta0.induct) auto

lemma inert_not_en: "inert M \<Longrightarrow> \<not> en M"
  by (cases rule: inert.cases) auto

lemma fb_rb: "tm M \<Longrightarrow> (inert M \<longrightarrow> dinert (rb M DVar)) \<and> (fb M \<longrightarrow> dfb (rb M DVar))"
proof (induction M)
  case (Var x)
  then show ?case by (auto intro: dinert_dfb.intros)
next
  case (Lam x M)
  then show ?case by (auto intro: dinert_dfb.intros)
next
  case (App M1 M2)
  then show ?case
    by (auto simp: inert_App_iff fb_App_iff dinert_DApp_iff intro: dinert_dfb.intros)
next
  case Id then show ?case by simp
next
  case (Extn M1 x M2) then show ?case by simp
next
  case (Nm y) then show ?case by simp
next
  case (Comp M1 M2)
  have i: "\<not> inert (Comp M1 M2)"
  proof
    assume "inert (Comp M1 M2)"
    then obtain x where "M1 = Var x" "inert M2" by (auto elim: inert.cases)
    then show False using Comp.prems inert_not_en by simp
  qed
  moreover have "dfb (rb (Comp M1 M2) DVar)" if "fb (Comp M1 M2)"
    using that
  proof (cases rule: fb_cases)
    case inert then show ?thesis using i by simp
  next
    case (clo x B L) then show ?thesis by (simp add: dinert_dfb.intros)
  qed auto
  ultimately show ?case by blast
qed

lemma beta_sorted:
  "beta0 M N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> rb M DVar \<rightarrow>\<^sub>f rb N DVar"
proof (induction rule: beta0.induct)
  case (Beta1 N x M L)
  have f: "dfb (rb N DVar)" using fb_rb Beta1 by simp
  have "rb (App (Comp (Lam x M) L) N) DVar \<rightarrow>\<^sub>f rb (Comp M (Extn N x L)) DVar"
    using vbeta[OF f, of "rb M ((\<lambda>y. lift (rbe L DVar y) 0)(x := DVar 0))"]
    by (simp add: beta_rb)
  then show ?case using Beta1 by simp
next
  case (Beta2 N x M)
  have f: "dfb (rb N DVar)" using fb_rb Beta2 by simp
  have eq: "(rb M ((\<lambda>y. lift (DVar y) 0)(x := DVar 0)))[rb N DVar/0] = rb M (DVar(x := rb N DVar))"
    by (rule beta_rb)
  have "DApp (DAbs (rb M ((\<lambda>y. lift (DVar y) 0)(x := DVar 0)))) (rb N DVar) \<rightarrow>\<^sub>f
      rb M (DVar(x := rb N DVar))"
    using vbeta[OF f, of "rb M ((\<lambda>y. lift (DVar y) 0)(x := DVar 0))"] eq by metis
  then have "rb (App (Lam x M) N) DVar \<rightarrow>\<^sub>f rb (Comp M (Extn N x Id)) DVar"
    by simp
  then show ?case using Beta2 by simp
next
  case (AppL M N L)
  then show ?case by (auto intro: vappL)
next
  case (AppR L M N)
  have "dfb (rb L DVar)" using fb_rb AppR by simp
  then show ?case using AppR by (auto intro: vappR)
next
  case (VarR M N x)
  then show ?case using beta_not_en by auto
qed

lemma rb_cbv_sorted:
  assumes "M \<rightarrow>\<^sub>v N" "tm M"
  shows "tm N \<and> (rb N DVar = rb M DVar \<and> tlength N < tlength M \<or> rb M DVar \<rightarrow>\<^sub>f rb N DVar)"
proof -
  from assms have c0: "cbv0 M N" using sorted_cbv_iff by blast
  show ?thesis
  proof (cases "M \<rightarrow>\<^sub>\<sigma> N")
    case True
    then have s0: "sig0 M N" using sorted_sig_iff assms(2) by blast
    show ?thesis using sig_sorted[OF s0] assms(2) sig_tlength_decrease[OF True] by blast
  next
    case False
    then have "M \<rightarrow>\<^sub>\<beta> N" using assms(1) by (auto simp: cbv_def)
    then have "beta0 M N" using sorted_beta_iff assms(2) by blast
    then show ?thesis using beta_sorted assms(2) by blast
  qed
qed

lemma rb_cbv_steps_sorted:
  "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> tm M \<Longrightarrow> tm N \<and> vred\<^sup>*\<^sup>* (rb M DVar) (rb N DVar)"
proof (induction rule: rtranclp_induct)
  case base then show ?case by simp
next
  case (step N P)
  then show ?case using rb_cbv_sorted[of N P] by (auto intro: rtranclp.rtrancl_into_rtrancl)
qed

subsection \<open>Conservativity\<close>

lemma CFN_imp_lam_VN:
  assumes t: "tm M" and c: "CFN M"
  shows "lam_VN (rb M DVar)"
proof -
  obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and f: "fb N" using c by (auto simp: CFN_def)
  from rb_cbv_steps_sorted[OF r t] have tN: "tm N" and h: "vred\<^sup>*\<^sup>* (rb M DVar) (rb N DVar)"
    by blast+
  have "dfb (rb N DVar)" using fb_rb tN f by blast
  then have "normal vred (rb N DVar)" using dfb_normal by blast
  then show ?thesis unfolding lam_VN_def using h by blast
qed

lemma vdist_imp_SN: "vdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> SN_at cbv M"
proof (induction n arbitrary: M rule: less_induct)
  case (less n)
  note IHn = less.IH
  have "\<And>M. vdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> SN_at cbv M"
  proof -
    fix M
    show "vdist (rb M DVar) n \<Longrightarrow> tm M \<Longrightarrow> SN_at cbv M"
    proof (induction "tlength M" arbitrary: M rule: less_induct)
      case less
      show ?case
      proof (rule SN_atI)
        fix N
        assume s: "M \<rightarrow>\<^sub>v N"
        from rb_cbv_sorted[OF s \<open>tm M\<close>] have tN: "tm N"
          and c: "rb N DVar = rb M DVar \<and> tlength N < tlength M \<or> rb M DVar \<rightarrow>\<^sub>f rb N DVar"
          by blast+
        from c show "SN_at cbv N"
        proof
          assume a: "rb N DVar = rb M DVar \<and> tlength N < tlength M"
          then have "vdist (rb N DVar) n" using less.prems(1) by simp
          then show ?thesis using less.hyps a tN by blast
        next
          assume "rb M DVar \<rightarrow>\<^sub>f rb N DVar"
          then obtain m where "n = Suc m" "vdist (rb N DVar) m"
            using vdist_step less.prems(1) by blast
          then show ?thesis using IHn tN by blast
        qed
      qed
    qed
  qed
  then show ?case using less.prems by blast
qed

lemma lam_VN_imp_CFSN: "tm M \<Longrightarrow> lam_VN (rb M DVar) \<Longrightarrow> CFSN M"
proof -
  assume t: "tm M" and w: "lam_VN (rb M DVar)"
  then obtain n where "vdist (rb M DVar) n" using lam_VN_vdist by blast
  then have "SN_at cbv M" using t vdist_imp_SN by blast
  moreover have "fb N" if r: "M \<rightarrow>\<^sub>v\<^sup>* N" and n: "NF N" for N
  proof -
    have "tm N" using cbv_steps_sorted[OF r t] by blast
    then show ?thesis using sorted_NF_fb n by blast
  qed
  ultimately show ?thesis by (auto simp: CFSN_def)
qed

theorem conservativity_sorted:
  assumes "tm M"
  shows "(lam_VN (rb M DVar) \<longleftrightarrow> CFN M) \<and> (CFN M \<longleftrightarrow> CFSN M) \<and> (Typ M \<longleftrightarrow> CFN M)"
  using assms CFN_imp_lam_VN lam_VN_imp_CFSN CFSN_imp_CFN main_characterization by blast
theorem conservativity:
  assumes "pure M"
  shows "Typ M \<longleftrightarrow> lam_VN (rb M DVar)"
    and "lam_VN (rb M DVar) \<longleftrightarrow> CFSN M"
  using conservativity_sorted[OF pure_tm[OF assms]] CFN_iff_CFSN by blast+

text \<open>Oracle check for the conservativity results.\<close>

ML \<open>
  val ths = [@{thm conservative_CFN}, @{thm conservative_Typ}, @{thm sorted_cbv_iff},
             @{thm conservativity_sorted}] @ @{thms conservativity};
  val oracles = Thm_Deps.all_oracles ths;
  val _ = if null oracles then writeln "No oracles."
          else if Config.get @{context} quick_and_dirty
          then warning ("Oracles used (quick_and_dirty): " ^ commas (map (#1 o #1) oracles))
          else error ("Oracles used: " ^ commas (map (#1 o #1) oracles));
\<close>

end
