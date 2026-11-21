theory Completeness
  imports Typing Uniform
begin

section \<open>Completeness: \<open>CFN M \<Longrightarrow> Typ M\<close>\<close>

text \<open>Adapted from the completeness proofs of call-by-value \<open>\<lambda>env\<close> (context refinement
  \<open>exp_top\<close>) and of call-by-name \<open>\<lambda>penv\<close>
  (name rules).  The refinement must keep the context free of name types.\<close>

subsection \<open>\<open>\<sigma>\<close>-expansion: replacing a subterm by one with at least the same typings\<close>

definition at_least :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "at_least M N \<longleftrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A)"

lemma rep_AppL_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App N L \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> App M L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_AppL: "at_least M N \<Longrightarrow> at_least (App M L) (App N L)"
  unfolding at_least_def by (blast intro: rep_AppL_aux)

lemma rep_AppR_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App L N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> App L M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_AppR: "at_least M N \<Longrightarrow> at_least (App L M) (App L N)"
  unfolding at_least_def by (blast intro: rep_AppR_aux)

lemma rep_Lam_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Lam x N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Lam x M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_Lam: "at_least M N \<Longrightarrow> at_least (Lam x M) (Lam x N)"
  unfolding at_least_def by (blast intro: rep_Lam_aux)

lemma rep_CompL_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Comp N L \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Comp M L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_CompL: "at_least M N \<Longrightarrow> at_least (Comp M L) (Comp N L)"
  unfolding at_least_def by (blast intro: rep_CompL_aux)

lemma rep_CompR_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Comp L N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Comp L M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_CompR: "at_least M N \<Longrightarrow> at_least (Comp L M) (Comp L N)"
  unfolding at_least_def by (blast intro: rep_CompR_aux)

lemma rep_ExtnL_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Extn N x L \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Extn M x L : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_ExtnL: "at_least M N \<Longrightarrow> at_least (Extn M x L) (Extn N x L)"
  unfolding at_least_def by (blast intro: rep_ExtnL_aux)

lemma rep_ExtnR_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Extn L x N \<Longrightarrow> (\<forall>C A. C \<turnstile> N : A \<longrightarrow> C \<turnstile> M : A) \<Longrightarrow>
     C \<turnstile> Extn L x M : A"
  by (induction rule: hasty.induct) (auto intro: hasty.intros)

lemma rep_ExtnR: "at_least M N \<Longrightarrow> at_least (Extn L x M) (Extn L x N)"
  unfolding at_least_def by (blast intro: rep_ExtnR_aux)

subsection \<open>Root rules\<close>

lemma exp_Ass: "at_least (Comp (Comp L M) N) (Comp L (Comp M N))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp L (Comp M N) : A"
  then obtain D where 1: "C \<turnstile> Comp M N : D" and 2: "D \<turnstile> L : A"
    using gen_Comp by blast
  from 1 obtain D' where 3: "C \<turnstile> N : D'" and 4: "D' \<turnstile> M : D"
    using gen_Comp by blast
  from 4 2 have "D' \<turnstile> Comp L M : A" by (rule TComp)
  with 3 show "C \<turnstile> Comp (Comp L M) N : A" by (rule TComp)
qed

lemma exp_IdL: "at_least (Comp Id M) M"
  unfolding at_least_def by (blast intro: TComp TId)

lemma exp_IdR: "at_least (Comp M Id) M"
  unfolding at_least_def by (blast intro: TComp TId)

lemma exp_VarRef: "at_least (Comp (Var x) (Extn M x N)) M"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> M : A"
  then have "C \<turnstile> Extn M x N : Env ((x, A) # []) False"
    by (rule TExtn[OF _ typ_env_om])
  moreover have "Env [(x, A)] False \<turnstile> Var x : A"
    by (rule TVar[OF s_refl]) simp
  ultimately show "C \<turnstile> Comp (Var x) (Extn M x N) : A"
    by (rule TComp)
qed

lemma exp_VarSkip: "x \<noteq> y \<Longrightarrow> at_least (Comp (Var y) (Extn M x N)) (Comp (Var y) N)"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume xy: "x \<noteq> y" and "C \<turnstile> Comp (Var y) N : A"
  then obtain D where 1: "C \<turnstile> N : D" and 2: "D \<turnstile> Var y : A"
    using gen_Comp by blast
  from gen_Var[OF 2 refl] show "C \<turnstile> Comp (Var y) (Extn M x N) : A"
  proof
    assume "Om \<preceq> A"
    then show ?thesis by (blast intro: TSub TOm)
  next
    assume "\<exists>m ob B. D \<preceq> Env m ob \<and> map_of m y = Some B \<and> B \<preceq> A"
    then obtain m ob B where d: "D \<preceq> Env m ob" and l: "map_of m y = Some B" and b: "B \<preceq> A"
      by blast
    have "C \<turnstile> N : Env m ob" using 1 d by (rule TSub)
    then have "C \<turnstile> Extn M x N : Env ((x, Om) # m) ob" by (rule TExtn[OF TOm])
    moreover have "Env ((x, Om) # m) ob \<turnstile> Var y : A"
    proof -
      have "map_of ((x, Om) # m) y = Some B" using l xy by simp
      then have "Env ((x, Om) # m) ob \<turnstile> Var y : B" by (rule TVar[OF s_refl])
      then show ?thesis using b by (rule TSub)
    qed
    ultimately show ?thesis by (rule TComp)
  qed
qed

lemma exp_DExtn: "at_least (Comp (Extn L x M) N) (Extn (Comp L N) x (Comp M N))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Extn (Comp L N) x (Comp M N) : A"
  then obtain B m ob where 1: "C \<turnstile> Comp L N : B" and 2: "C \<turnstile> Comp M N : Env m ob"
    and s: "Env ((x, B) # m) ob \<preceq> A"
    using gen_Extn by blast
  from 1 obtain D1 where a: "C \<turnstile> N : D1" "D1 \<turnstile> L : B" using gen_Comp by blast
  from 2 obtain D2 where b: "C \<turnstile> N : D2" "D2 \<turnstile> M : Env m ob" using gen_Comp by blast
  have "C \<turnstile> N : Inter D1 D2" using a(1) b(1) by (rule TInter)
  moreover have "Inter D1 D2 \<turnstile> Extn L x M : Env ((x, B) # m) ob"
  proof (rule TExtn)
    show "Inter D1 D2 \<turnstile> L : B" by (rule narrowing[OF a(2) s_il])
    show "Inter D1 D2 \<turnstile> M : Env m ob" by (rule narrowing[OF b(2) s_ir])
  qed
  ultimately have "C \<turnstile> Comp (Extn L x M) N : Env ((x, B) # m) ob" by (rule TComp)
  from this s show "C \<turnstile> Comp (Extn L x M) N : A" by (rule TSub)
qed

lemma exp_DApp_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App (Comp M1 N) (Comp M2 N) \<Longrightarrow> C \<turnstile> Comp (App M1 M2) N : A"
proof (induction rule: hasty.induct)
  case (TApp C P A B Q)
  then have p: "C \<turnstile> Comp M1 N : Arr A B" and q: "C \<turnstile> Comp M2 N : A" and e: "ess A" by auto
  from p obtain D1 where a: "C \<turnstile> N : D1" "D1 \<turnstile> M1 : Arr A B" using gen_Comp by blast
  from q obtain D2 where b: "C \<turnstile> N : D2" "D2 \<turnstile> M2 : A" using gen_Comp by blast
  have "C \<turnstile> N : Inter D1 D2" using a(1) b(1) by (rule TInter)
  moreover have "Inter D1 D2 \<turnstile> App M1 M2 : B"
  proof (rule hasty.TApp)
    show "Inter D1 D2 \<turnstile> M1 : Arr A B" by (rule narrowing[OF a(2) s_il])
    show "Inter D1 D2 \<turnstile> M2 : A" by (rule narrowing[OF b(2) s_ir])
    show "ess A" by (rule e)
  qed
  ultimately show ?case by (rule TComp)
qed (auto intro: hasty.intros)

lemma exp_DApp: "at_least (Comp (App M1 M2) N) (App (Comp M1 N) (Comp M2 N))"
  unfolding at_least_def using exp_DApp_aux by blast

lemma env_cons_sub:
  "B1 \<preceq> B2 \<Longrightarrow> Env ((y, B1) # m) ob \<preceq> Env ((y, B2) # m) ob"
proof (rule s_env)
  assume "B1 \<preceq> B2"
  then show "\<forall>z A'. map_of ((y, B2) # m) z = Some A' \<longrightarrow>
      (\<exists>A. map_of ((y, B1) # m) z = Some A \<and> A \<preceq> A')"
    by (auto intro: s_refl)
qed simp

lemma exp_AppConst: "at_least (App M (Nm x)) (Comp (Var x) M)"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp (Var x) M : A"
  then obtain D where 1: "C \<turnstile> M : D" and 2: "D \<turnstile> Var x : A"
    using gen_Comp by blast
  from gen_Var[OF 2 refl] show "C \<turnstile> App M (Nm x) : A"
  proof
    assume "Om \<preceq> A"
    then show ?thesis by (blast intro: TSub TOm)
  next
    assume "\<exists>m ob B. D \<preceq> Env m ob \<and> map_of m x = Some B \<and> B \<preceq> A"
    then obtain m ob B where d: "D \<preceq> Env m ob" and l: "map_of m x = Some B" and b: "B \<preceq> A"
      by blast
    have "Env m ob \<preceq> Arr (QN x) B" by (rule s_envarr[OF l])
    moreover have "Arr (QN x) B \<preceq> Arr (QN x) A" by (rule s_arr[OF s_refl b])
    ultimately have "D \<preceq> Arr (QN x) A" using d by (blast intro: s_trans)
    with 1 have "C \<turnstile> M : Arr (QN x) A" by (rule TSub)
    then show ?thesis by (rule TApp) (simp_all add: TNm)
  qed
qed

lemma exp_ConstComp: "at_least (Comp (Nm x) L) (Nm x)"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Nm x : A"
  then have "QN x \<preceq> A" using gen_Nm by blast
  then have "Om \<turnstile> Nm x : A" by (rule TSub[OF TNm])
  moreover have "C \<turnstile> L : Om" by (rule TOm)
  ultimately show "C \<turnstile> Comp (Nm x) L : A" by (blast intro: TComp)
qed

lemma exp_VarLam: "at_least (Comp (Var x) (Lam y M)) (Comp M (Extn (Nm x) y Id))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp M (Extn (Nm x) y Id) : A"
  then obtain D where 1: "C \<turnstile> Extn (Nm x) y Id : D" and 2: "D \<turnstile> M : A"
    using gen_Comp by blast
  from 1 obtain B m ob where n: "C \<turnstile> Nm x : B" and l: "C \<turnstile> Id : Env m ob"
    and s: "Env ((y, B) # m) ob \<preceq> D"
    using gen_Extn by blast
  have q: "QN x \<preceq> B" using gen_Nm[OF n refl] .
  have c: "C \<preceq> Env m ob" using gen_Id[OF l refl] .
  have "Env ((y, QN x) # m) ob \<preceq> D" using env_cons_sub[OF q] s by (rule s_trans)
  with 2 have "Env ((y, QN x) # m) ob \<turnstile> M : A" by (rule narrowing)
  then have "C \<turnstile> Lam y M : Arr (QN x) A" by (rule TLam[OF c])
  then have "C \<turnstile> Lam y M : Env [(x, A)] False" using s_arrenv by (rule TSub)
  moreover have "Env [(x, A)] False \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
  ultimately show "C \<turnstile> Comp (Var x) (Lam y M) : A" by (rule TComp)
qed

lemma exp_VarClos:
  "at_least (Comp (Var x) (Comp (Lam y M) L)) (Comp M (Extn (Nm x) y L))"
  unfolding at_least_def
proof (intro allI impI)
  fix C A
  assume "C \<turnstile> Comp M (Extn (Nm x) y L) : A"
  then obtain D where 1: "C \<turnstile> Extn (Nm x) y L : D" and 2: "D \<turnstile> M : A"
    using gen_Comp by blast
  from 1 obtain B m ob where n: "C \<turnstile> Nm x : B" and l: "C \<turnstile> L : Env m ob"
    and s: "Env ((y, B) # m) ob \<preceq> D"
    using gen_Extn by blast
  have q: "QN x \<preceq> B" using gen_Nm[OF n refl] .
  have "Env ((y, QN x) # m) ob \<preceq> D" using env_cons_sub[OF q] s by (rule s_trans)
  with 2 have "Env ((y, QN x) # m) ob \<turnstile> M : A" by (rule narrowing)
  then have "Env m ob \<turnstile> Lam y M : Arr (QN x) A" by (rule TLam[OF s_refl])
  with l have "C \<turnstile> Comp (Lam y M) L : Arr (QN x) A" by (rule TComp)
  then have "C \<turnstile> Comp (Lam y M) L : Env [(x, A)] False" using s_arrenv by (rule TSub)
  moreover have "Env [(x, A)] False \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
  ultimately show "C \<turnstile> Comp (Var x) (Comp (Lam y M) L) : A" by (rule TComp)
qed

subsection \<open>Subject expansion for \<open>\<sigma>\<close>\<close>

lemma sig_expansion: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> at_least M N"
proof (induction rule: sig.induct)
  case (Ass L M N) show ?case by (rule exp_Ass)
next
  case (IdL M) show ?case by (rule exp_IdL)
next
  case (IdR M) show ?case by (rule exp_IdR)
next
  case (DExtn L x M N) show ?case by (rule exp_DExtn)
next
  case (VarRef x M N) show ?case by (rule exp_VarRef)
next
  case (VarSkip x y M N) then show ?case by (rule exp_VarSkip)
next
  case (DApp M1 M2 N) show ?case by (rule exp_DApp)
next
  case (AppConst M x) show ?case by (rule exp_AppConst)
next
  case (ConstComp x L) show ?case by (rule exp_ConstComp)
next
  case (AppL M N L) then show ?case by (blast intro: rep_AppL)
next
  case (AppR M N L) then show ?case by (blast intro: rep_AppR)
next
  case (Lam M N x) then show ?case by (blast intro: rep_Lam)
next
  case (CompL M N L) then show ?case by (blast intro: rep_CompL)
next
  case (CompR M N L) then show ?case by (blast intro: rep_CompR)
next
  case (ExtnL M N x L) then show ?case by (blast intro: rep_ExtnL)
next
  case (ExtnR M N L x) then show ?case by (blast intro: rep_ExtnR)
qed

lemma subject_expansion_sig: "M \<rightarrow>\<^sub>\<sigma> N \<Longrightarrow> C \<turnstile> N : A \<Longrightarrow> C \<turnstile> M : A"
  using sig_expansion by (auto simp: at_least_def)

subsection \<open>Refining the top-level context\<close>

text \<open>
  As in call-by-value \<open>\<lambda>env\<close>, refinement of the top-level context.  The refined
  context must stay free of name types (\<open>qm\<close>), since \<open>Typ\<close> requires it.
\<close>

definition qm :: "(var \<times> ty) list \<Rightarrow> bool" where
  "qm m \<longleftrightarrow> (\<forall>p \<in> set m. qfree (snd p))"

lemma qm_Nil [simp]: "qm []" by (simp add: qm_def)

lemma qm_Cons [simp]: "qm ((x, A) # m) \<longleftrightarrow> qfree A \<and> qm m" by (simp add: qm_def)

lemma qm_emeet: "qm m1 \<Longrightarrow> qm m2 \<Longrightarrow> qm (emeet m1 m2)"
  unfolding qm_def
proof
  fix p assume a: "\<forall>p\<in>set m1. qfree (snd p)" "\<forall>p\<in>set m2. qfree (snd p)" and p: "p \<in> set (emeet m1 m2)"
  from p have "p \<in> set m2 \<or> (\<exists>x A. (x, A) \<in> set m1 \<and>
      p = (x, case map_of m2 x of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A))"
    by (auto simp: emeet_def)
  then show "qfree (snd p)"
  proof
    assume "p \<in> set m2" then show ?thesis using a(2) by blast
  next
    assume "\<exists>x A. (x, A) \<in> set m1 \<and> p = (x, case map_of m2 x of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A)"
    then obtain x A where xa: "(x, A) \<in> set m1"
      and p': "p = (x, case map_of m2 x of Some B \<Rightarrow> Inter A B | None \<Rightarrow> A)" by blast
    have qA: "qfree A" using a(1) xa by force
    show ?thesis
    proof (cases "map_of m2 x")
      case None then show ?thesis using p' qA by simp
    next
      case (Some B)
      then have "(x, B) \<in> set m2" by (rule map_of_SomeD)
      then have "qfree B" using a(2) by force
      then show ?thesis using p' Some qA by simp
    qed
  qed
qed

lemma emeet_sub1: "Env (emeet m1 m2) ob \<preceq> Env m1 ob"
proof (rule s_env)
  show "\<forall>x A'. map_of m1 x = Some A' \<longrightarrow> (\<exists>A. map_of (emeet m1 m2) x = Some A \<and> A \<preceq> A')"
    by (auto simp: map_of_emeet intro: s_il s_refl split: option.split)
qed simp

lemma emeet_sub2: "Env (emeet m1 m2) ob \<preceq> Env m2 ob"
proof (rule s_env)
  show "\<forall>x A'. map_of m2 x = Some A' \<longrightarrow> (\<exists>A. map_of (emeet m1 m2) x = Some A \<and> A \<preceq> A')"
    by (auto simp: map_of_emeet intro: s_ir s_refl split: option.split)
qed simp

lemma sub_env_head: "B \<preceq> B' \<Longrightarrow> Env ((x, B) # m) ob \<preceq> Env ((x, B') # m) ob"
  by (rule env_cons_sub)

definition exp_top :: "trm \<Rightarrow> trm \<Rightarrow> bool" where
  "exp_top M N \<longleftrightarrow>
     (\<forall>m ob A. qm m \<longrightarrow> Env m ob \<turnstile> N : A \<longrightarrow>
        (\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> M : A))"

lemma exp_topI:
  "(\<And>m ob A. qm m \<Longrightarrow> Env m ob \<turnstile> N : A \<Longrightarrow>
      \<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> M : A) \<Longrightarrow>
   exp_top M N"
  unfolding exp_top_def by blast

lemma exp_topD:
  "exp_top M N \<Longrightarrow> qm m \<Longrightarrow> Env m ob \<turnstile> N : A \<Longrightarrow>
     \<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> M : A"
  unfolding exp_top_def by blast

lemma at_least_top: "at_least M N \<Longrightarrow> exp_top M N"
  unfolding at_least_def by (rule exp_topI) (blast intro: s_refl)

lemma refine_meet:
  assumes "qm m1" "Env m1 ob \<preceq> Env m ob" "Env m1 ob \<turnstile> M : A"
    "qm m2" "Env m2 ob \<preceq> Env m ob" "Env m2 ob \<turnstile> M : B"
  shows "\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> M : Inter A B"
proof -
  have 1: "Env (emeet m1 m2) ob \<turnstile> M : A" using narrowing[OF assms(3) emeet_sub1] .
  have 2: "Env (emeet m1 m2) ob \<turnstile> M : B" using narrowing[OF assms(6) emeet_sub2] .
  have "Env (emeet m1 m2) ob \<preceq> Env m ob" using emeet_sub1 assms(2) by (rule s_trans)
  then show ?thesis using TInter[OF 1 2] qm_emeet[OF assms(1) assms(4)] by blast
qed

lemma rep_AppL_top_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App N L \<Longrightarrow> C = Env m ob \<Longrightarrow> qm m \<Longrightarrow> exp_top M N \<Longrightarrow>
     \<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> App M L : A"
proof (induction arbitrary: m rule: hasty.induct)
  case (TApp C P A B Q)
  then have n: "Env m ob \<turnstile> N : Arr A B" and l: "Env m ob \<turnstile> L : A" and e: "ess A" by auto
  from exp_topD[OF TApp.prems(4) TApp.prems(3) n] obtain m' where q: "qm m'"
    and s: "Env m' ob \<preceq> Env m ob" and t: "Env m' ob \<turnstile> M : Arr A B" by blast
  have "Env m' ob \<turnstile> L : A" using narrowing[OF l s] .
  then show ?case using q s t e by (blast intro: hasty.TApp)
next
  case (TOm C P)
  then show ?case by (blast intro: hasty.TOm s_refl)
next
  case (TInter C P A B)
  then obtain m1 m2 where "qm m1" "Env m1 ob \<preceq> Env m ob" "Env m1 ob \<turnstile> App M L : A"
    "qm m2" "Env m2 ob \<preceq> Env m ob" "Env m2 ob \<turnstile> App M L : B" by blast
  then show ?case by (rule refine_meet)
next
  case (TSub C P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma rep_AppL_top: "exp_top M N \<Longrightarrow> exp_top (App M L) (App N L)"
  by (rule exp_topI) (rule rep_AppL_top_aux[OF _ refl refl])

lemma rep_AppR_top_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = App L N \<Longrightarrow> C = Env m ob \<Longrightarrow> qm m \<Longrightarrow> exp_top M N \<Longrightarrow>
     \<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> App L M : A"
proof (induction arbitrary: m rule: hasty.induct)
  case (TApp C P A B Q)
  then have l: "Env m ob \<turnstile> L : Arr A B" and n: "Env m ob \<turnstile> N : A" and e: "ess A" by auto
  from exp_topD[OF TApp.prems(4) TApp.prems(3) n] obtain m' where q: "qm m'"
    and s: "Env m' ob \<preceq> Env m ob" and t: "Env m' ob \<turnstile> M : A" by blast
  have "Env m' ob \<turnstile> L : Arr A B" using narrowing[OF l s] .
  then show ?case using q s t e by (blast intro: hasty.TApp)
next
  case (TOm C P)
  then show ?case by (blast intro: hasty.TOm s_refl)
next
  case (TInter C P A B)
  then obtain m1 m2 where "qm m1" "Env m1 ob \<preceq> Env m ob" "Env m1 ob \<turnstile> App L M : A"
    "qm m2" "Env m2 ob \<preceq> Env m ob" "Env m2 ob \<turnstile> App L M : B" by blast
  then show ?case by (rule refine_meet)
next
  case (TSub C P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma rep_AppR_top: "exp_top M N \<Longrightarrow> exp_top (App L M) (App L N)"
  by (rule exp_topI) (rule rep_AppR_top_aux[OF _ refl refl])

lemma rep_VarR_top_aux:
  "C \<turnstile> P : A \<Longrightarrow> P = Comp (Var x) N \<Longrightarrow> C = Env m ob \<Longrightarrow> qm m \<Longrightarrow> exp_top M N \<Longrightarrow>
     \<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> Comp (Var x) M : A"
proof (induction arbitrary: m rule: hasty.induct)
  case (TComp C Q D K A)
  then have n: "Env m ob \<turnstile> N : D" and v: "D \<turnstile> Var x : A" by auto
  from exp_topD[OF TComp.prems(4) TComp.prems(3) n] obtain m' where q: "qm m'"
    and s: "Env m' ob \<preceq> Env m ob" and t: "Env m' ob \<turnstile> M : D" by blast
  then show ?case using v by (blast intro: hasty.TComp)
next
  case (TOm C P)
  then show ?case by (blast intro: hasty.TOm s_refl)
next
  case (TInter C P A B)
  then obtain m1 m2 where "qm m1" "Env m1 ob \<preceq> Env m ob" "Env m1 ob \<turnstile> Comp (Var x) M : A"
    "qm m2" "Env m2 ob \<preceq> Env m ob" "Env m2 ob \<turnstile> Comp (Var x) M : B" by blast
  then show ?case by (rule refine_meet)
next
  case (TSub C P A B)
  then show ?case by (blast intro: hasty.TSub)
qed auto

lemma rep_VarR_top: "exp_top M N \<Longrightarrow> exp_top (Comp (Var x) M) (Comp (Var x) N)"
  by (rule exp_topI) (rule rep_VarR_top_aux[OF _ refl refl])

subsection \<open>Fireballs have essential types\<close>

text \<open>
  Inert terms are typable at every name-free type; fireballs have an essential type that
  is name-free unless the fireball is itself a quoted name.  The refined context is
  name-free.
\<close>

lemma lam_typable: "C \<preceq> Env m ob \<Longrightarrow> C \<turnstile> Lam x M : Arr Om Om"
  by (rule TLam) (auto intro: TOm)

lemma emeet_single_lookup: "\<exists>B. map_of (emeet m [(x, A)]) x = Some B \<and> B \<preceq> A"
  by (auto simp: map_of_emeet intro: s_ir s_refl split: option.split)

lemma emeet_nonempty: "emeet m [(x, A)] \<noteq> []"
  by (simp add: emeet_def)

lemma qm_emeet_single: "qm m \<Longrightarrow> qfree A \<Longrightarrow> qm (emeet m [(x, A)])"
  by (rule qm_emeet) simp_all

definition fbty :: "trm \<Rightarrow> (var \<times> ty) list \<Rightarrow> bool \<Rightarrow> bool" where
  "fbty M m ob \<longleftrightarrow> (\<exists>m' T. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> ess T \<and> Env m' ob \<turnstile> M : T \<and>
         (qfree T \<or> (\<exists>y. M = Nm y \<and> T = QN y)))"

lemma fbty_same:
  "Env m ob \<turnstile> M : T \<Longrightarrow> qm m \<Longrightarrow> ess T \<Longrightarrow> (qfree T \<or> (\<exists>y. M = Nm y \<and> T = QN y)) \<Longrightarrow>
   fbty M m ob"
  unfolding fbty_def by (blast intro: s_refl)

lemma fbty_inert:
  assumes "qm m'" "Env m' ob \<preceq> Env m ob" "Env m' ob \<turnstile> M : TV 0"
  shows "fbty M m ob"
  unfolding fbty_def using assms by (intro exI[of _ m'] exI[of _ "TV 0"]) simp

lemma inert_fb_typable:
  "(inert M \<longrightarrow> (\<forall>m ob A. qm m \<longrightarrow> qfree A \<longrightarrow>
      (\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> M : A))) \<and>
   (fb M \<longrightarrow> (\<forall>m ob. qm m \<longrightarrow> fbty M m ob))"
  (is "?I M \<and> ?F M")
proof (induction M)
  case (Var x)
  have i: "?I (Var x)"
  proof (intro impI allI)
    fix m ob A
    assume q: "qm m" "qfree A"
    obtain B where l: "map_of (emeet m [(x, A)]) x = Some B" and b: "B \<preceq> A"
      using emeet_single_lookup by blast
    have "Env (emeet m [(x, A)]) ob \<turnstile> Var x : A" using TSub[OF TVar[OF s_refl l] b] .
    moreover have "qm (emeet m [(x, A)])" using qm_emeet_single[OF q] .
    ultimately show "\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> Var x : A"
      using emeet_sub1 by blast
  qed
  have "?F (Var x)"
  proof (intro impI allI)
    fix m ob
    assume "qm m"
    from i[rule_format, where m=m and ob=ob and A="TV 0", OF IVar \<open>qm m\<close>] obtain m' where
      "qm m'" "Env m' ob \<preceq> Env m ob" "Env m' ob \<turnstile> Var x : TV 0" by auto
    then show "fbty (Var x) m ob" by (rule fbty_inert)
  qed
  with i show ?case by blast
next
  case (Lam x M)
  have "\<not> inert (Lam x M)" by (auto elim: inert.cases)
  moreover have "?F (Lam x M)"
  proof (intro impI allI)
    fix m ob
    assume "qm m"
    have "Env m ob \<turnstile> Lam x M : Arr Om Om" by (rule lam_typable[OF s_refl])
    then show "fbty (Lam x M) m ob" using \<open>qm m\<close> by (rule fbty_same) simp_all
  qed
  ultimately show ?case by blast
next
  case (App M1 M2)
  have i: "?I (App M1 M2)"
  proof (intro impI allI)
    fix m ob A
    assume "inert (App M1 M2)" and qm: "qm m" and qA: "qfree A"
    then have a1: "inert M1" and a2: "fb M2" by (simp_all add: inert_App_iff)
    from App.IH(2) a2 qm have "fbty M2 m ob" by blast
    then obtain m1 T where q1: "qm m1" and s1: "Env m1 ob \<preceq> Env m ob"
      and e: "ess T" and t1: "Env m1 ob \<turnstile> M2 : T"
      and T: "qfree T \<or> (\<exists>y. M2 = Nm y \<and> T = QN y)" unfolding fbty_def by blast
    from T show "\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> App M1 M2 : A"
    proof
      assume qT: "qfree T"
      from qT qA have qa: "qfree (Arr T A)" by simp
      from App.IH(1) have "?I M1" by blast
      from this[rule_format, where m=m1 and ob=ob and A="Arr T A", OF a1 q1 qa] obtain m2 where q2: "qm m2"
        and s2: "Env m2 ob \<preceq> Env m1 ob" and t2: "Env m2 ob \<turnstile> M1 : Arr T A" by blast
      have "Env m2 ob \<turnstile> M2 : T" using narrowing[OF t1 s2] .
      then have "Env m2 ob \<turnstile> App M1 M2 : A" using t2 e by (blast intro: TApp)
      moreover have "Env m2 ob \<preceq> Env m ob" using s2 s1 by (rule s_trans)
      ultimately show ?thesis using q2 by blast
    next
      assume "\<exists>y. M2 = Nm y \<and> T = QN y"
      then obtain y where y: "M2 = Nm y" by blast
      have qa: "qfree (Env [(y, A)] True)" using qA by simp
      from App.IH(1) have "?I M1" by blast
      from this[rule_format, where m=m1 and ob=ob and A="Env [(y, A)] True", OF a1 q1 qa] obtain m2 where q2: "qm m2"
        and s2: "Env m2 ob \<preceq> Env m1 ob" and t2: "Env m2 ob \<turnstile> M1 : Env [(y, A)] True" by blast
      have "map_of [(y, A)] y = Some A" by simp
      then have "Env [(y, A)] True \<preceq> Arr (QN y) A" by (rule s_envarr)
      with t2 have "Env m2 ob \<turnstile> M1 : Arr (QN y) A" by (rule TSub)
      moreover have "Env m2 ob \<turnstile> M2 : QN y" using y by (simp add: TNm)
      ultimately have "Env m2 ob \<turnstile> App M1 M2 : A" by (rule TApp) simp
      moreover have "Env m2 ob \<preceq> Env m ob" using s2 s1 by (rule s_trans)
      ultimately show ?thesis using q2 by blast
    qed
  qed
  have "?F (App M1 M2)"
  proof (intro impI allI)
    fix m ob
    assume "fb (App M1 M2)" and "qm m"
    then have "inert (App M1 M2)" by (simp add: fb_App_iff inert_App_iff)
    from i[rule_format, where m=m and ob=ob and A="TV 0", OF this \<open>qm m\<close>] obtain m' where
      "qm m'" "Env m' ob \<preceq> Env m ob" "Env m' ob \<turnstile> App M1 M2 : TV 0" by auto
    then show "fbty (App M1 M2) m ob" by (rule fbty_inert)
  qed
  with i show ?case by blast
next
  case Id
  have "\<not> inert Id" by (auto elim: inert.cases)
  moreover have "?F Id"
  proof (intro impI allI)
    fix m ob
    assume "qm m"
    have q: "qm (emeet m [(0, Om)])" using qm_emeet_single[OF \<open>qm m\<close>] by simp
    have t: "Env (emeet m [(0, Om)]) ob \<turnstile> Id : Env (emeet m [(0, Om)]) ob" by (rule TId)
    have e: "ess (Env (emeet m [(0, Om)]) ob)" using emeet_nonempty by simp
    have f: "qfree (Env (emeet m [(0, Om)]) ob)" using q by (simp add: qm_def)
    show "fbty Id m ob" unfolding fbty_def
      by (rule exI[of _ "emeet m [(0, Om)]"], rule exI[of _ "Env (emeet m [(0, Om)]) ob"])
         (use q t e f emeet_sub1 in blast)
  qed
  ultimately show ?case by blast
next
  case (Extn M1 x M2)
  have "\<not> inert (Extn M1 x M2)" by (auto elim: inert.cases)
  moreover have "?F (Extn M1 x M2)"
  proof (intro impI allI)
    fix m ob
    assume "qm m"
    have "Env m ob \<turnstile> Extn M1 x M2 : Env [(x, Om)] False"
      by (rule TExtn[OF TOm typ_env_om])
    then show "fbty (Extn M1 x M2) m ob" using \<open>qm m\<close> by (rule fbty_same) (simp_all add: qm_def)
  qed
  ultimately show ?case by blast
next
  case (Nm y)
  have "\<not> inert (Nm y)" by simp
  moreover have "?F (Nm y)"
  proof (intro impI allI)
    fix m ob
    assume "qm m"
    have "Env m ob \<turnstile> Nm y : QN y" by (rule TNm)
    then show "fbty (Nm y) m ob" using \<open>qm m\<close> by (rule fbty_same) simp_all
  qed
  ultimately show ?case by blast
next
  case (Comp M1 M2)
  have i: "?I (Comp M1 M2)"
  proof (intro impI allI)
    fix m ob A
    assume "inert (Comp M1 M2)" and qm: "qm m" and qA: "qfree A"
    then obtain x where m1: "M1 = Var x" and a2: "inert M2" by (auto elim: inert.cases)
    have qa: "qfree (Env [(x, A)] True)" using qA by simp
    from Comp.IH(2) have "?I M2" by blast
    from this[rule_format, where m=m and ob=ob and A="Env [(x, A)] True", OF a2 qm qa] obtain m' where q: "qm m'"
      and s: "Env m' ob \<preceq> Env m ob" and t: "Env m' ob \<turnstile> M2 : Env [(x, A)] True" by blast
    have "Env [(x, A)] True \<turnstile> Var x : A" by (rule TVar[OF s_refl]) simp
    then have "Env m' ob \<turnstile> Comp M1 M2 : A" using t m1 by (blast intro: TComp)
    then show "\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> Comp M1 M2 : A"
      using s q by blast
  qed
  have "?F (Comp M1 M2)"
  proof (intro impI allI)
    fix m ob
    assume f: "fb (Comp M1 M2)" and qm: "qm m"
    show "fbty (Comp M1 M2) m ob" using f
    proof (cases rule: fb_cases)
      case inert
      from i[rule_format, where m=m and ob=ob and A="TV 0", OF inert qm] obtain m' where
        "qm m'" "Env m' ob \<preceq> Env m ob" "Env m' ob \<turnstile> Comp M1 M2 : TV 0" by auto
      then show ?thesis by (rule fbty_inert)
    next
      case (clo x B L)
      have "Env m ob \<turnstile> L : Env [] False" by (rule typ_env_om)
      moreover have "Env [] False \<turnstile> Lam x B : Arr Om Om" by (rule lam_typable[OF s_refl])
      ultimately have "Env m ob \<turnstile> Comp M1 M2 : Arr Om Om" using clo by (blast intro: TComp)
      then show ?thesis using qm by (rule fbty_same) simp_all
    qed simp_all
  qed
  with i show ?case by blast
qed

lemma fb_typable:
  "fb M \<Longrightarrow> qm m \<Longrightarrow> \<exists>m' T. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> ess T \<and> Env m' ob \<turnstile> M : T"
  using inert_fb_typable unfolding fbty_def by blast

subsection \<open>\<open>\<beta>\<^sub>v\<close>-expansion\<close>

lemma exp_Beta2_top: "fb V \<Longrightarrow> exp_top (App (Lam x B) V) (Comp B (Extn V x Id))"
proof (rule exp_topI)
  fix m ob A
  assume f: "fb V" and qm: "qm m" and "Env m ob \<turnstile> Comp B (Extn V x Id) : A"
  then obtain D where 1: "Env m ob \<turnstile> Extn V x Id : D" and 2: "D \<turnstile> B : A"
    using gen_Comp by blast
  from 1 obtain T m1 o1 where v: "Env m ob \<turnstile> V : T" and i: "Env m ob \<turnstile> Id : Env m1 o1"
    and s: "Env ((x, T) # m1) o1 \<preceq> D"
    using gen_Extn by blast
  have c: "Env m ob \<preceq> Env m1 o1" using gen_Id[OF i refl] .
  from fb_typable[OF f qm] obtain m' T' where q: "qm m'" and s': "Env m' ob \<preceq> Env m ob"
    and e: "ess T'" and v': "Env m' ob \<turnstile> V : T'" by blast
  have vv: "Env m' ob \<turnstile> V : Inter T T'" using TInter[OF narrowing[OF v s'] v'] .
  have "Env ((x, Inter T T') # m1) o1 \<preceq> D" using sub_env_head[OF s_il] s by (rule s_trans)
  then have "Env ((x, Inter T T') # m1) o1 \<turnstile> B : A" by (rule narrowing[OF 2])
  then have "Env m' ob \<turnstile> Lam x B : Arr (Inter T T') A" using s_trans[OF s' c] by (blast intro: TLam)
  then have "Env m' ob \<turnstile> App (Lam x B) V : A" using vv e by (auto intro: TApp)
  then show "\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> App (Lam x B) V : A"
    using q s' by blast
qed

lemma exp_Beta1_top: "fb V \<Longrightarrow> exp_top (App (Comp (Lam x B) L) V) (Comp B (Extn V x L))"
proof (rule exp_topI)
  fix m ob A
  assume f: "fb V" and qm: "qm m" and "Env m ob \<turnstile> Comp B (Extn V x L) : A"
  then obtain D where 1: "Env m ob \<turnstile> Extn V x L : D" and 2: "D \<turnstile> B : A"
    using gen_Comp by blast
  from 1 obtain T m1 o1 where v: "Env m ob \<turnstile> V : T" and l: "Env m ob \<turnstile> L : Env m1 o1"
    and s: "Env ((x, T) # m1) o1 \<preceq> D"
    using gen_Extn by blast
  from fb_typable[OF f qm] obtain m' T' where q: "qm m'" and s': "Env m' ob \<preceq> Env m ob"
    and e: "ess T'" and v': "Env m' ob \<turnstile> V : T'" by blast
  have vv: "Env m' ob \<turnstile> V : Inter T T'" using TInter[OF narrowing[OF v s'] v'] .
  have "Env ((x, Inter T T') # m1) o1 \<preceq> D" using sub_env_head[OF s_il] s by (rule s_trans)
  then have "Env ((x, Inter T T') # m1) o1 \<turnstile> B : A" by (rule narrowing[OF 2])
  then have "Env m1 o1 \<turnstile> Lam x B : Arr (Inter T T') A" by (blast intro: TLam s_refl)
  then have "Env m' ob \<turnstile> Comp (Lam x B) L : Arr (Inter T T') A"
    using narrowing[OF l s'] by (blast intro: TComp)
  then have "Env m' ob \<turnstile> App (Comp (Lam x B) L) V : A" using vv e by (auto intro: TApp)
  then show "\<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> App (Comp (Lam x B) L) V : A"
    using q s' by blast
qed

lemma beta_expansion_top: "M \<rightarrow>\<^sub>\<beta> N \<Longrightarrow> exp_top M N"
proof (induction rule: beta.induct)
  case (Beta1 N x M L) show ?case using Beta1.hyps by (rule exp_Beta1_top)
next
  case (Beta2 N x M) show ?case using Beta2.hyps by (rule exp_Beta2_top)
next
  case (AppL M N L) show ?case using AppL.IH by (rule rep_AppL_top)
next
  case (AppR L M N) show ?case using AppR.IH by (rule rep_AppR_top)
next
  case (VarClos x y M L) show ?case by (rule at_least_top[OF exp_VarClos])
next
  case (VarLam x y M) show ?case by (rule at_least_top[OF exp_VarLam])
next
  case (VarR M N x) show ?case using VarR.IH by (rule rep_VarR_top)
qed

subsection \<open>Subject expansion and completeness\<close>

lemma subject_expansion_top:
  "M \<rightarrow>\<^sub>v N \<Longrightarrow> qm m \<Longrightarrow> Env m ob \<turnstile> N : A \<Longrightarrow>
     \<exists>m'. qm m' \<and> Env m' ob \<preceq> Env m ob \<and> Env m' ob \<turnstile> M : A"
proof -
  assume s: "M \<rightarrow>\<^sub>v N" and q: "qm m" and t: "Env m ob \<turnstile> N : A"
  from s consider "M \<rightarrow>\<^sub>\<sigma> N" | "M \<rightarrow>\<^sub>\<beta> N" by (auto simp: cbv_def)
  then show ?thesis
  proof cases
    case 1 then show ?thesis using subject_expansion_sig[OF 1 t] s_refl q by blast
  next
    case 2 then show ?thesis using exp_topD[OF beta_expansion_top[OF 2] q t] by blast
  qed
qed

lemma subject_expansion_steps:
  "M \<rightarrow>\<^sub>v\<^sup>* N \<Longrightarrow> qm m \<Longrightarrow> Env m ob \<turnstile> N : A \<Longrightarrow> \<exists>m'. qm m' \<and> Env m' ob \<turnstile> M : A"
proof (induction arbitrary: m rule: converse_rtranclp_induct)
  case base then show ?case by blast
next
  case (step M M')
  then obtain m1 where "qm m1" "Env m1 ob \<turnstile> M' : A" by blast
  then show ?case using subject_expansion_top[OF step.hyps(1)] by blast
qed

lemma fb_Typ: "fb M \<Longrightarrow> Typ M"
  using fb_typable[of M "[]" True] qm_Nil by (auto simp: Typ_def qm_def)

theorem completeness: "CFN M \<Longrightarrow> Typ M"
proof -
  assume "CFN M"
  then obtain N where r: "M \<rightarrow>\<^sub>v\<^sup>* N" and c: "fb N" by (auto simp: CFN_def)
  from fb_typable[OF c qm_Nil, of True] obtain m T where q: "qm m"
    and t: "Env m True \<turnstile> N : T" and e: "ess T" by blast
  from subject_expansion_steps[OF r q t] obtain m' where "qm m'" "Env m' True \<turnstile> M : T" by blast
  with e show "Typ M" by (auto simp: Typ_def qm_def)
qed

end
