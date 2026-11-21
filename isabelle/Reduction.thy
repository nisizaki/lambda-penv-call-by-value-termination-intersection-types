theory Reduction
  imports Sigma
begin

section \<open>Call-by-value reduction: full \<open>\<sigma>\<close> plus left-to-right \<open>\<beta>\<^sub>v\<close>\<close>

subsection \<open>Fireballs\<close>

text \<open>
  Fireballs (in the sense of open call-by-value) are values and inert terms.
  Values are abstractions, closures, \<open>id\<close> and environment extensions; the
  components of closures and extensions are not evaluated (environments are lazy).
  Inert terms are variables, applications of inert terms to fireballs, and
  variable look-ups in inert environments.  No \<open>\<sigma>\<close>-normality is required.
\<close>

inductive inert :: "trm \<Rightarrow> bool" and fb :: "trm \<Rightarrow> bool" where
  IVar: "inert (Var x)"
| IApp: "inert M \<Longrightarrow> fb N \<Longrightarrow> inert (App M N)"
| IComp: "inert M \<Longrightarrow> inert (Comp (Var x) M)"
| FInert: "inert M \<Longrightarrow> fb M"
| FLam: "fb (Lam x M)"
| FClo: "fb (Comp (Lam x M) L)"
| FId: "fb Id"
| FExtn: "fb (Extn M x L)"
| FNm: "fb (Nm x)"

lemma fb_Var [simp]: "fb (Var x)" by (rule FInert[OF IVar])

lemma inert_App_iff: "inert (App M N) \<longleftrightarrow> inert M \<and> fb N"
proof
  assume "inert (App M N)"
  then show "inert M \<and> fb N" by (cases rule: inert.cases) simp_all
next
  assume "inert M \<and> fb N"
  then show "inert (App M N)" by (blast intro: IApp)
qed

lemma fb_App_iff: "fb (App M N) \<longleftrightarrow> inert M \<and> fb N"
proof
  assume "fb (App M N)"
  then have "inert (App M N)" by (cases rule: fb.cases) simp_all
  then show "inert M \<and> fb N" by (simp add: inert_App_iff)
next
  assume "inert M \<and> fb N"
  then show "fb (App M N)" by (blast intro: IApp FInert)
qed

lemma fb_cases:
  assumes "fb M"
  obtains (inert) "inert M" | (lam) x B where "M = Lam x B"
  | (clo) x B L where "M = Comp (Lam x B) L" | (id) "M = Id" | (extn) N x L where "M = Extn N x L"
  | (nm) y where "M = Nm y"
  using assms by (cases rule: fb.cases) auto

lemma not_inert [simp]:
  "\<not> inert (Lam x B)" "\<not> inert (Comp (Lam x B) L)" "\<not> inert Id" "\<not> inert (Extn N x L)"
  "\<not> inert (Nm y)"
  by (auto elim: inert.cases)

lemma inert_not_Lam: "inert M \<Longrightarrow> M \<noteq> Lam x B"
  by (auto elim: inert.cases)

lemma inert_not_Clo: "inert M \<Longrightarrow> M \<noteq> Comp (Lam x B) L"
  by (auto elim: inert.cases)

lemma inert_not_Extn: "inert M \<Longrightarrow> M \<noteq> Extn N x L"
  by (auto elim: inert.cases)

lemma inert_not_Id: "inert M \<Longrightarrow> M \<noteq> Id"
  by (auto elim: inert.cases)

subsection \<open>\<open>\<beta>\<^sub>v\<close>\<close>

text \<open>
  The argument of a \<open>\<beta>\<^sub>v\<close>-redex must be a fireball.  \<open>\<beta>\<^sub>v\<close> works in the function part
  of an application, in the argument once the function part is a fireball, and in the
  environment of a variable look-up (\<open>VarR\<close>).  It does not work under \<open>\<lambda>\<close>, inside
  environment extensions or closure environments, or on the left of a composition.
\<close>

inductive beta :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<beta>" 50) where
  Beta1: "fb N \<Longrightarrow> App (Comp (Lam x M) L) N \<rightarrow>\<^sub>\<beta> Comp M (Extn N x L)"
| Beta2: "fb N \<Longrightarrow> App (Lam x M) N \<rightarrow>\<^sub>\<beta> Comp M (Extn N x Id)"
| AppL: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> App M L \<rightarrow>\<^sub>\<beta> App N L"
| AppR: "fb L \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> App L M \<rightarrow>\<^sub>\<beta> App L N"
| VarClos: "Comp (Var x) (Comp (Lam y M) L) \<rightarrow>\<^sub>\<beta> Comp M (Extn (Nm x) y L)"
| VarLam: "Comp (Var x) (Lam y M) \<rightarrow>\<^sub>\<beta> Comp M (Extn (Nm x) y Id)"
| VarR: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>\<beta> Comp (Var x) N"

definition cbv :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>v" 50) where
  "M \<rightarrow>\<^sub>v N \<longleftrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<or> M \<rightarrow>\<^sub>\<beta> N"

abbreviation cbv_steps :: "trm \<Rightarrow> trm \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>v\<^sup>*" 50) where
  "M \<rightarrow>\<^sub>v\<^sup>* N \<equiv> cbv\<^sup>*\<^sup>* M N"

abbreviation NF :: "trm \<Rightarrow> bool" where "NF M \<equiv> normal cbv M"

lemma sig_imp_cbv: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> M \<rightarrow>\<^sub>v N" by (simp add: cbv_def)
lemma beta_imp_cbv: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> M \<rightarrow>\<^sub>v N" by (simp add: cbv_def)

subsection \<open>Fireballs are closed under \<open>\<sigma>\<close> and have no \<open>\<beta>\<^sub>v\<close>-redex\<close>

lemma sig_inert_fb:
  "(inert M \<longrightarrow> (\<forall>N. M \<rightarrow>\<^sub>\<sigma> N \<longrightarrow> inert N)) \<and> (fb M \<longrightarrow> (\<forall>N. M \<rightarrow>\<^sub>\<sigma> N \<longrightarrow> fb N))"
proof (induction M)
  case (Var x)
  have "\<not> Var x \<rightarrow>\<^sub>\<sigma> N" for N by (auto elim: sig.cases)
  then show ?case by blast
next
  case (Lam x M)
  have "fb N" if "Lam x M \<rightarrow>\<^sub>\<sigma> N" for N
    using that by (cases rule: sig.cases) (simp add: FLam)
  moreover have "\<not> inert (Lam x M)" by (auto elim: inert.cases)
  ultimately show ?case by blast
next
  case (App M1 M2)
  have i: "inert N" if "inert (App M1 M2)" "App M1 M2 \<rightarrow>\<^sub>\<sigma> N" for N
  proof -
    from that(1) have a: "inert M1" "fb M2" by (simp_all add: inert_App_iff)
    from that(2) show ?thesis
    proof (cases rule: sig.cases)
      case (AppL M1')
      then show ?thesis using App.IH(1) a by (simp add: inert_App_iff)
    next
      case (AppR M2')
      then show ?thesis using App.IH(2) a by (simp add: inert_App_iff)
    next
      case (AppConst y)
      then show ?thesis using a IComp by simp
    qed
  qed
  moreover have "fb N" if "fb (App M1 M2)" "App M1 M2 \<rightarrow>\<^sub>\<sigma> N" for N
  proof -
    have "inert (App M1 M2)" using that(1) by (simp add: fb_App_iff inert_App_iff)
    then show ?thesis using i that(2) FInert by blast
  qed
  ultimately show ?case by blast
next
  case Id
  have "\<not> Id \<rightarrow>\<^sub>\<sigma> N" for N by (auto elim: sig.cases)
  then show ?case by blast
next
  case (Extn M1 x M2)
  have "fb N" if "Extn M1 x M2 \<rightarrow>\<^sub>\<sigma> N" for N
    using that by (cases rule: sig.cases) (simp_all add: FExtn)
  moreover have "\<not> inert (Extn M1 x M2)" by (auto elim: inert.cases)
  ultimately show ?case by blast
next
  case (Nm y)
  have "\<not> Nm y \<rightarrow>\<^sub>\<sigma> N" for N by (auto elim: sig.cases)
  then show ?case by blast
next
  case (Comp M1 M2)
  have i: "inert N" if "inert (Comp M1 M2)" "Comp M1 M2 \<rightarrow>\<^sub>\<sigma> N" for N
  proof -
    from that(1) obtain x where m1: "M1 = Var x" and m2: "inert M2"
      by (auto elim: inert.cases)
    from that(2) show ?thesis
    proof (cases rule: sig.cases)
      case IdR
      then show ?thesis using m2 inert_not_Id by blast
    next
      case (VarRef K)
      then show ?thesis using m2 m1 inert_not_Extn by blast
    next
      case (VarSkip z y K L)
      then show ?thesis using m2 m1 inert_not_Extn by blast
    next
      case (CompL M1')
      then show ?thesis using m1 by (auto elim: sig.cases)
    next
      case (CompR M2')
      then show ?thesis using Comp.IH(2) m1 m2 IComp by blast
    qed (use m1 in simp_all)
  qed
  moreover have "fb N" if "fb (Comp M1 M2)" "Comp M1 M2 \<rightarrow>\<^sub>\<sigma> N" for N
    using that(1)
  proof (cases rule: fb_cases)
    case inert
    then show ?thesis using i that(2) FInert by blast
  next
    case (clo x B L)
    from that(2)[unfolded clo] show ?thesis
    proof (cases rule: sig.cases)
      case IdR then show ?thesis by (simp add: FLam)
    next
      case (CompL M1')
      then obtain B' where "M1' = Lam x B'" by (auto elim: sig.cases)
      then show ?thesis using CompL by (simp add: FClo)
    next
      case (CompR M2')
      then show ?thesis by (simp add: FClo)
    qed
  qed simp_all
  ultimately show ?case by blast
qed

lemma sig_fb: "fb M \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> fb N"
  using sig_inert_fb by blast

lemma sig_inert: "inert M \<Longrightarrow> M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> inert N"
  using sig_inert_fb by blast

lemma sig_steps_fb: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> fb M \<Longrightarrow> fb N"
  by (induction rule: rtranclp_induct) (auto intro: sig_fb)

lemma Var_no_beta: "Var x \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta.cases)
lemma Id_no_beta: "Id \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta.cases)
lemma Lam_no_beta: "Lam x M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta.cases)
lemma Extn_no_beta: "Extn M x L \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta.cases)
lemma Clo_no_beta: "Comp (Lam x M) L \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta.cases)
lemma Nm_no_beta: "Nm y \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> False"
  by (auto elim: beta.cases)

lemma inert_fb_no_beta:
  "(inert M \<longrightarrow> (\<forall>N. \<not> M \<rightarrow>\<^sub>\<beta> N)) \<and> (fb M \<longrightarrow> (\<forall>N. \<not> M \<rightarrow>\<^sub>\<beta> N))"
proof (induction M)
  case (App M1 M2)
  have i: "\<not> App M1 M2 \<rightarrow>\<^sub>\<beta> N" if "inert (App M1 M2)" for N
  proof
    assume b: "App M1 M2 \<rightarrow>\<^sub>\<beta> N"
    from that have a: "inert M1" "fb M2" by (simp_all add: inert_App_iff)
    from b show False
    proof (cases rule: beta.cases)
      case (Beta1 x M L) then show False using a inert_not_Clo by blast
    next
      case (Beta2 x M) then show False using a inert_not_Lam by blast
    next
      case (AppL N') then show False using App.IH(1) a by blast
    next
      case (AppR N') then show False using App.IH(2) a by blast
    qed
  qed
  then show ?case by (auto simp: fb_App_iff inert_App_iff)
next
  case (Comp M1 M2)
  have i: "\<not> Comp M1 M2 \<rightarrow>\<^sub>\<beta> N" if "inert (Comp M1 M2)" for N
  proof
    assume b: "Comp M1 M2 \<rightarrow>\<^sub>\<beta> N"
    from that obtain x where "M1 = Var x" and m2: "inert M2" by (auto elim: inert.cases)
    from b show False
    proof (cases rule: beta.cases)
      case (VarR N') then show False using Comp.IH(2) m2 by blast
    next
      case (VarClos x' y B L) then show False using m2 inert_not_Clo by blast
    next
      case (VarLam x' y B) then show False using m2 inert_not_Lam by blast
    qed
  qed
  have "\<not> Comp M1 M2 \<rightarrow>\<^sub>\<beta> N" if "fb (Comp M1 M2)" for N
    using that
  proof (cases rule: fb_cases)
    case inert then show ?thesis using i by blast
  next
    case (clo x B L) then show ?thesis using Clo_no_beta by blast
  qed auto
  then show ?case using i by blast
qed (auto elim: beta.cases simp: fb_App_iff)

lemma fb_no_beta: "fb M \<Longrightarrow> \<not> M \<rightarrow>\<^sub>\<beta> N"
  using inert_fb_no_beta by blast

subsection \<open>\<open>\<beta>\<^sub>v\<close> is deterministic\<close>

lemma beta_det: "M \<rightarrow>\<^sub>\<beta> N1 \<Longrightarrow> M \<rightarrow>\<^sub>\<beta> N2 \<Longrightarrow> N1 = N2"
proof (induction arbitrary: N2 rule: beta.induct)
  case (Beta1 N x M L)
  from Beta1.prems show ?case
    using fb_no_beta[OF Beta1.hyps] by (cases rule: beta.cases) (auto dest: Clo_no_beta)
next
  case (Beta2 N x M)
  from Beta2.prems show ?case
    using fb_no_beta[OF Beta2.hyps] by (cases rule: beta.cases) (auto dest: Lam_no_beta)
next
  case (AppL M N L)
  from AppL.prems show ?case
  proof (cases rule: beta.cases)
    case (Beta1 x B K) then show ?thesis using AppL.hyps Clo_no_beta by blast
  next
    case (Beta2 x B) then show ?thesis using AppL.hyps Lam_no_beta by blast
  next
    case (AppL N') then show ?thesis using AppL.IH by simp
  next
    case (AppR N') then show ?thesis using AppL.hyps fb_no_beta by blast
  qed
next
  case (AppR L M N)
  from AppR.prems show ?case
  proof (cases rule: beta.cases)
    case (Beta1 x B K) then show ?thesis using AppR.hyps fb_no_beta by blast
  next
    case (Beta2 x B) then show ?thesis using AppR.hyps fb_no_beta by blast
  next
    case (AppL L') then show ?thesis using AppR.hyps fb_no_beta by blast
  next
    case (AppR N') then show ?thesis using AppR.IH by simp
  qed
next
  case (VarClos x y B L)
  from VarClos.prems show ?case
    by (cases rule: beta.cases) (auto dest: Clo_no_beta)
next
  case (VarLam x y B)
  from VarLam.prems show ?case
    by (cases rule: beta.cases) (auto dest: Lam_no_beta)
next
  case (VarR M N x)
  from VarR.prems show ?case
  proof (cases rule: beta.cases)
    case (VarClos y B L) then show ?thesis using VarR.hyps Clo_no_beta by blast
  next
    case (VarLam y B) then show ?thesis using VarR.hyps Lam_no_beta by blast
  next
    case (VarR N') then show ?thesis using VarR.IH by simp
  qed
qed

subsection \<open>Congruences for reduction sequences\<close>

lemma steps_lift:
  assumes "\<And>P Q. R P Q \<Longrightarrow> R' (f P) (f Q)"
  shows "R\<^sup>*\<^sup>* M N \<Longrightarrow> R'\<^sup>*\<^sup>* (f M) (f N)"
  by (induction rule: rtranclp_induct) (auto intro: rtranclp.rtrancl_into_rtrancl assms)

lemma cbv_AppL: "M \<rightarrow>\<^sub>v N \<Longrightarrow> App M L \<rightarrow>\<^sub>v App N L"
  by (auto simp: cbv_def intro: sig.AppL beta.AppL)

lemma cbv_VarR: "M \<rightarrow>\<^sub>v N \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>v Comp (Var x) N"
  by (auto simp: cbv_def intro: sig.CompR beta.VarR)

lemma cbv_steps_AppL: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> App M N \<rightarrow>\<^sub>v\<^sup>* App M' N"
  by (rule steps_lift[of cbv cbv "\<lambda>P. App P N"]) (rule cbv_AppL)

lemma cbv_steps_VarR: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> Comp (Var x) M \<rightarrow>\<^sub>v\<^sup>* Comp (Var x) M'"
  by (rule steps_lift[of cbv cbv "\<lambda>P. Comp (Var x) P"]) (rule cbv_VarR)

lemma cbv_steps_AppR:
  assumes "fb L"
  shows "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> App L M \<rightarrow>\<^sub>v\<^sup>* App L M'"
  by (rule steps_lift[of cbv cbv "\<lambda>P. App L P"]) (auto simp: cbv_def intro: sig.AppR beta.AppR assms)

lemma sig_steps_cbv: "sig\<^sup>*\<^sup>* M N \<Longrightarrow> M \<rightarrow>\<^sub>v\<^sup>* N"
  by (rule steps_lift[of sig cbv "\<lambda>P. P"]) (rule sig_imp_cbv)

lemma sig_steps_lift:
  assumes "\<And>P Q. P \<rightarrow>\<^sub>\<sigma> Q \<Longrightarrow> f P \<rightarrow>\<^sub>\<sigma> f Q"
  shows "sig\<^sup>*\<^sup>* M N \<Longrightarrow> sig\<^sup>*\<^sup>* (f M) (f N)"
  by (rule steps_lift[of sig sig f]) (rule assms)

end
