theory Lambda
  imports ARS
begin

section \<open>Pure \<open>\<lambda>\<close>-calculus (de Bruijn) and open call-by-value\<close>

text \<open>
  Definitions of \<open>lift\<close> and \<open>subst\<close> follow the Isabelle distribution
  (\<^verbatim>\<open>HOL/Proofs/Lambda/Lambda.thy\<close>), with constructors renamed.
\<close>

datatype dB =
    DVar nat
  | DApp dB dB
  | DAbs dB

primrec lift :: "dB \<Rightarrow> nat \<Rightarrow> dB" where
  "lift (DVar i) k = (if i < k then DVar i else DVar (i + 1))"
| "lift (DApp s t) k = DApp (lift s k) (lift t k)"
| "lift (DAbs s) k = DAbs (lift s (k + 1))"

primrec subst :: "dB \<Rightarrow> dB \<Rightarrow> nat \<Rightarrow> dB" ("_[_'/_]" [300, 0, 0] 300) where
  subst_Var: "(DVar i)[s/k] = (if k < i then DVar (i - 1) else if i = k then s else DVar i)"
| subst_App: "(DApp t u)[s/k] = DApp (t[s/k]) (u[s/k])"
| subst_Abs: "(DAbs t)[s/k] = DAbs (t[lift s 0 / k + 1])"

declare subst_Var [simp del]

lemma subst_eq [simp]: "(DVar k)[u/k] = u"
  by (simp add: subst_Var)

lemma subst_gt [simp]: "i < j \<Longrightarrow> (DVar j)[u/i] = DVar (j - 1)"
  by (simp add: subst_Var)

lemma subst_lt [simp]: "j < i \<Longrightarrow> (DVar j)[u/i] = DVar j"
  by (simp add: subst_Var)

lemma lift_lift:
  "i < k + 1 \<Longrightarrow> lift (lift t i) (Suc k) = lift (lift t k) i"
  by (induct t arbitrary: i k) auto

lemma lift_subst_lt:
  "i < j + 1 \<Longrightarrow> lift (t[s/j]) i = (lift t i) [lift s i / j + 1]"
  by (induct t arbitrary: i j s) (auto simp: lift_lift subst_Var)

lemma subst_lift [simp]: "(lift t k)[s/k] = t"
  by (induct t arbitrary: k s) simp_all

subsection \<open>Open call-by-value (the fireball calculus), left-to-right\<close>

text \<open>
  Fireballs are abstractions and inert terms (variables applied to fireballs).
  \<open>\<beta>\<^sub>f\<close> fires when the argument is a fireball; evaluation is weak and left-to-right.
  On closed terms fireballs are exactly the values, and this is Plotkin's
  left-to-right call-by-value evaluation.
\<close>

inductive dinert :: "dB \<Rightarrow> bool" and dfb :: "dB \<Rightarrow> bool" where
  "dinert (DVar i)"
| "dinert s \<Longrightarrow> dfb t \<Longrightarrow> dinert (DApp s t)"
| "dinert s \<Longrightarrow> dfb s"
| "dfb (DAbs s)"

inductive vred :: "dB \<Rightarrow> dB \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>f" 50) where
  vbeta: "dfb t \<Longrightarrow> DApp (DAbs s) t \<rightarrow>\<^sub>f s[t/0]"
| vappL: "s \<rightarrow>\<^sub>f s' \<Longrightarrow> DApp s t \<rightarrow>\<^sub>f DApp s' t"
| vappR: "dfb s \<Longrightarrow> t \<rightarrow>\<^sub>f t' \<Longrightarrow> DApp s t \<rightarrow>\<^sub>f DApp s t'"

lemma dinert_not_DAbs [simp]: "\<not> dinert (DAbs s)"
  by (auto elim: dinert.cases)

lemma dinert_DApp_iff: "dinert (DApp s t) \<longleftrightarrow> dinert s \<and> dfb t"
  by (auto elim: dinert.cases intro: dinert_dfb.intros)

lemma dfb_DApp_iff: "dfb (DApp s t) \<longleftrightarrow> dinert s \<and> dfb t"
proof
  assume "dfb (DApp s t)"
  then have "dinert (DApp s t)" by (cases rule: dfb.cases) simp_all
  then show "dinert s \<and> dfb t" by (simp add: dinert_DApp_iff)
qed (auto intro: dinert_dfb.intros)

lemma dfb_normal: "(dinert s \<longrightarrow> normal vred s) \<and> (dfb s \<longrightarrow> normal vred s)"
proof (induction s)
  case (DVar i)
  then show ?case by (auto simp: normal_def elim: vred.cases)
next
  case (DApp s t)
  have "normal vred (DApp s t)" if "dinert s" "dfb t"
  proof (rule normalI)
    fix u show "\<not> DApp s t \<rightarrow>\<^sub>f u"
    proof
      assume "DApp s t \<rightarrow>\<^sub>f u"
      then show False
        using that DApp.IH by (cases rule: vred.cases) (auto simp: normal_def)
    qed
  qed
  then show ?case by (auto simp: dinert_DApp_iff dfb_DApp_iff)
next
  case (DAbs s)
  then show ?case by (auto simp: normal_def elim: vred.cases)
qed

lemma dfb_no_vred: "dfb s \<Longrightarrow> \<not> s \<rightarrow>\<^sub>f t"
  using dfb_normal by (auto simp: normal_def)

lemma vred_det: "s \<rightarrow>\<^sub>f t \<Longrightarrow> s \<rightarrow>\<^sub>f u \<Longrightarrow> t = u"
proof (induction arbitrary: u rule: vred.induct)
  case (vbeta t s)
  from vbeta.prems show ?case
  proof (cases rule: vred.cases)
    case (vappL s') then show ?thesis by (auto elim: vred.cases)
  next
    case (vappR t') then show ?thesis using dfb_no_vred[OF vbeta.hyps] by blast
  qed simp
next
  case (vappL s s' t)
  from vappL.prems show ?case
  proof (cases rule: vred.cases)
    case (vbeta s0) then show ?thesis using vappL.hyps by (auto elim: vred.cases)
  next
    case (vappL s'') then show ?thesis using vappL.IH by simp
  next
    case (vappR t') then show ?thesis using vappL.hyps dfb_no_vred by blast
  qed
next
  case (vappR s t t')
  from vappR.prems show ?case
  proof (cases rule: vred.cases)
    case (vbeta s0) then show ?thesis using vappR.hyps dfb_no_vred by blast
  next
    case (vappL s'') then show ?thesis using vappR.hyps dfb_no_vred by blast
  next
    case (vappR t'') then show ?thesis using vappR.IH by simp
  qed
qed

definition lam_VN :: "dB \<Rightarrow> bool" where
  "lam_VN t \<longleftrightarrow> (\<exists>u. vred\<^sup>*\<^sup>* t u \<and> normal vred u)"

inductive vdist :: "dB \<Rightarrow> nat \<Rightarrow> bool" where
  vd0: "normal vred t \<Longrightarrow> vdist t 0"
| vdS: "t \<rightarrow>\<^sub>f u \<Longrightarrow> vdist u n \<Longrightarrow> vdist t (Suc n)"

lemma lam_VN_vdist: "lam_VN t \<Longrightarrow> \<exists>n. vdist t n"
proof -
  assume "lam_VN t"
  then obtain u where r: "vred\<^sup>*\<^sup>* t u" and nf: "normal vred u" by (auto simp: lam_VN_def)
  from r show ?thesis
  proof (induction rule: converse_rtranclp_induct)
    case base then show ?case using nf vd0 by blast
  next
    case (step y z) then show ?case using vdS by blast
  qed
qed

lemma vdist_step:
  assumes "vdist t n" "t \<rightarrow>\<^sub>f u"
  shows "\<exists>m. n = Suc m \<and> vdist u m"
  using assms(1)
proof (cases rule: vdist.cases)
  case vd0 then show ?thesis using assms(2) by (auto simp: normal_def)
next
  case (vdS u' m) then show ?thesis using assms(2) vred_det by blast
qed

end
