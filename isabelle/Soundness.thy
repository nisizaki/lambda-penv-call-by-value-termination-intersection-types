theory Soundness
  imports Completeness
begin

section \<open>Soundness: \<open>Typ M \<Longrightarrow> CFN M\<close>\<close>

text \<open>
  Realizability as for call-by-name weak-head normalization, with two changes: the
  interpretation of an arrow type only quantifies over normalizing arguments, and the
  interpretation of every type is closed under forward reduction as well, because an
  argument is evaluated before it is passed.  Forward closure follows from the
  uniqueness of normal forms (theory \<open>Uniform\<close>).
\<close>

subsection \<open>Normal forms of some shapes\<close>

lemma NF_Var: "NF (Var x)"
  by (auto simp: normal_def cbv_def elim: sig.cases beta.cases)

lemma NF_App_inert:
  assumes i: "inert I" and ni: "NF I" and f: "fb F" and nf: "NF F" and nn: "\<forall>y. F \<noteq> Nm y"
  shows "NF (App I F)"
proof (rule normalI)
  fix Q
  show "\<not> App I F \<rightarrow>\<^sub>v Q"
  proof
    assume "App I F \<rightarrow>\<^sub>v Q"
    then consider "App I F \<rightarrow>\<^sub>\<sigma> Q" | "App I F \<rightarrow>\<^sub>\<beta> Q" by (auto simp: cbv_def)
    then show False
    proof cases
      case 1
      then show False
        using ni nf nn by (cases rule: sig.cases) (auto simp: normal_def cbv_def)
    next
      case 2
      then show False
        using ni nf i inert_not_Lam inert_not_Clo
        by (cases rule: beta.cases) (auto simp: normal_def cbv_def)
    qed
  qed
qed

lemma NF_Comp_inert:
  assumes i: "inert I" and ni: "NF I"
  shows "NF (Comp (Var x) I)"
proof (rule normalI)
  fix Q
  show "\<not> Comp (Var x) I \<rightarrow>\<^sub>v Q"
  proof
    assume "Comp (Var x) I \<rightarrow>\<^sub>v Q"
    then consider "Comp (Var x) I \<rightarrow>\<^sub>\<sigma> Q" | "Comp (Var x) I \<rightarrow>\<^sub>\<beta> Q" by (auto simp: cbv_def)
    then show False
    proof cases
      case 1
      then show False
        using ni i inert_not_Id inert_not_Extn
        by (cases rule: sig.cases) (auto simp: normal_def cbv_def elim: sig.cases)
    next
      case 2
      then show False
        using ni i inert_not_Lam inert_not_Clo by (cases rule: beta.cases) (auto simp: normal_def cbv_def)
    qed
  qed
qed

lemma CFN_Nm: "CFN (Nm x)"
  by (auto simp: CFN_def intro: FNm NF_Nm)

lemma CFN_QN: "N \<rightarrow>\<^sub>v\<^sup>* Nm x \<Longrightarrow> CFN N"
  using CFN_back_steps CFN_Nm by blast

lemma cbv_AppConst: "App M (Nm x) \<rightarrow>\<^sub>v Comp (Var x) M"
  by (rule sig_imp_cbv[OF sig.AppConst])

lemma CFN_sig_fb: "fb M \<Longrightarrow> CFN M"
proof -
  assume f: "fb M"
  obtain N where s: "sig\<^sup>*\<^sup>* M N" and n: "sig_normal N" using sig_nf by blast
  have "fb N" using sig_steps_fb[OF s f] .
  then show "CFN M" using fb_NF[OF _ n] sig_steps_cbv[OF s] by (auto simp: CFN_def)
qed

lemma CFN_Lam: "CFN (Lam x M)" by (rule CFN_sig_fb[OF FLam])
lemma CFN_Extn: "CFN (Extn M x N)" by (rule CFN_sig_fb[OF FExtn])
lemma CFN_Clo: "CFN (Comp (Lam x M) e)" by (rule CFN_sig_fb[OF FClo])
lemma CFN_Id: "CFN Id" by (rule CFN_sig_fb[OF FId])

text \<open>Weak neutral terms.\<close>

inductive wneu :: "trm \<Rightarrow> bool" where
  "wneu (Var x)"
| "wneu M \<Longrightarrow> CFN N \<Longrightarrow> wneu (App M N)"
| "wneu M \<Longrightarrow> wneu (Comp (Var x) M)"

lemma wneu_reduces: "wneu M \<Longrightarrow> \<exists>I. M \<rightarrow>\<^sub>v\<^sup>* I \<and> NF I \<and> inert I"
proof (induction rule: wneu.induct)
  case (1 x)
  then show ?case using NF_Var IVar by blast
next
  case (2 M N)
  then obtain I where r1: "M \<rightarrow>\<^sub>v\<^sup>* I" and n1: "NF I" and i: "inert I" by blast
  from 2 obtain F where r2: "N \<rightarrow>\<^sub>v\<^sup>* F" and n2: "NF F" and f: "fb F" by (auto simp: CFN_def)
  have r3: "App M N \<rightarrow>\<^sub>v\<^sup>* App I F"
    using cbv_steps_AppL[OF r1] cbv_steps_AppR[OF FInert[OF i] r2] by (rule rtranclp_trans)
  show ?case
  proof (cases "\<exists>y. F = Nm y")
    case True
    then obtain y where y: "F = Nm y" by blast
    have "App I (Nm y) \<rightarrow>\<^sub>v Comp (Var y) I" by (rule cbv_AppConst)
    with r3 y have "App M N \<rightarrow>\<^sub>v\<^sup>* Comp (Var y) I" by (blast intro: rtranclp.rtrancl_into_rtrancl)
    moreover have "NF (Comp (Var y) I)" by (rule NF_Comp_inert[OF i n1])
    moreover have "inert (Comp (Var y) I)" using i by (rule IComp)
    ultimately show ?thesis by blast
  next
    case False
    then have nn: "\<forall>y. F \<noteq> Nm y" by blast
    have "NF (App I F)" by (rule NF_App_inert[OF i n1 f n2 nn])
    moreover have "inert (App I F)" using i f by (rule IApp)
    ultimately show ?thesis using r3 by blast
  qed
next
  case (3 M x)
  then obtain I where r1: "M \<rightarrow>\<^sub>v\<^sup>* I" and n1: "NF I" and i: "inert I" by blast
  have "Comp (Var x) M \<rightarrow>\<^sub>v\<^sup>* Comp (Var x) I" by (rule cbv_steps_VarR[OF r1])
  moreover have "NF (Comp (Var x) I)" by (rule NF_Comp_inert[OF i n1])
  moreover have "inert (Comp (Var x) I)" using i by (rule IComp)
  ultimately show ?case by blast
qed

lemma wneu_CFN: "wneu M \<Longrightarrow> CFN M"
  using wneu_reduces FInert by (auto simp: CFN_def)

subsection \<open>Interpretation of types\<close>

fun I :: "ty \<Rightarrow> trm set" where
  "I (TV n) = {M. CFN M}"
| "I Om = UNIV"
| "I (Arr A B) = {M. CFN M \<and> (\<forall>N \<in> I A. CFN N \<longrightarrow> App M N \<in> I B)}"
| "I (Inter A B) = I A \<inter> I B"
| "I (QN x) = {M. M \<rightarrow>\<^sub>v\<^sup>* Nm x}"
| "I (Env m ob) =
     {e. ((m \<noteq> [] \<or> ob) \<longrightarrow> CFN e) \<and>
         (\<forall>x S. map_of (map (\<lambda>(y, A). (y, I A)) m) x = Some S \<longrightarrow>
            Comp (Var x) e \<in> S \<and> (\<forall>N. N \<rightarrow>\<^sub>v\<^sup>* Nm x \<longrightarrow> App e N \<in> S))}"

lemma I_Env:
  "e \<in> I (Env m ob) \<longleftrightarrow>
     ((m \<noteq> [] \<or> ob) \<longrightarrow> CFN e) \<and>
     (\<forall>x A. map_of m x = Some A \<longrightarrow>
        Comp (Var x) e \<in> I A \<and> (\<forall>N \<in> I (QN x). App e N \<in> I A))"
  by (simp add: map_of_map_dep) blast

declare I.simps(6) [simp del]

lemma I_QN: "N \<in> I (QN x) \<longleftrightarrow> N \<rightarrow>\<^sub>v\<^sup>* Nm x"
  by simp

lemma I_back: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFN_back by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  have "CFN M" using Arr.prems CFN_back by simp
  moreover have "App M N \<in> I B" if "N \<in> I A" "CFN N" for N
  proof -
    have "App M' N \<in> I B" using Arr.prems that by simp
    then show ?thesis using Arr.IH(2)[OF cbv_AppL[OF Arr.prems(1)]] by blast
  qed
  ultimately show ?case by simp
next
  case (Inter A B) then show ?case by simp
next
  case (QN x) then show ?case by (simp add: converse_rtranclp_into_rtranclp)
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A \<and> (\<forall>N \<in> I (QN x). App M N \<in> I A)" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M' \<in> I A" and a: "\<And>N. N \<in> I (QN x) \<Longrightarrow> App M' N \<in> I A"
      using Env.prems(2) l by (simp_all add: I_Env)
    have "Comp (Var x) M \<in> I A" by (rule Env.IH[OF xa sn cbv_VarR[OF Env.prems(1)] c])
    moreover have "App M N \<in> I A" if "N \<in> I (QN x)" for N
      by (rule Env.IH[OF xa sn cbv_AppL[OF Env.prems(1)] a[OF that]])
    ultimately show ?thesis by blast
  qed
  then show ?case using Env.prems CFN_back by (simp add: I_Env)
qed

lemma I_back_steps: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> M' \<in> I A \<Longrightarrow> M \<in> I A"
  by (induction rule: converse_rtranclp_induct) (auto intro: I_back)

lemma I_fwd: "M \<rightarrow>\<^sub>v M' \<Longrightarrow> M \<in> I A \<Longrightarrow> M' \<in> I A"
proof (induction A arbitrary: M M')
  case (TV n) then show ?case using CFN_fwd by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  have "CFN M'" using Arr.prems CFN_fwd by simp
  moreover have "App M' N \<in> I B" if "N \<in> I A" "CFN N" for N
  proof -
    have "App M N \<in> I B" using Arr.prems that by simp
    then show ?thesis using Arr.IH(2)[OF cbv_AppL[OF Arr.prems(1)]] by blast
  qed
  ultimately show ?case by simp
next
  case (Inter A B) then show ?case by simp
next
  case (QN x) then show ?case using Nm_fwd by simp
next
  case (Env m ob)
  have "Comp (Var x) M' \<in> I A \<and> (\<forall>N \<in> I (QN x). App M' N \<in> I A)" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have c: "Comp (Var x) M \<in> I A" and a: "\<And>N. N \<in> I (QN x) \<Longrightarrow> App M N \<in> I A"
      using Env.prems(2) l by (simp_all add: I_Env)
    have "Comp (Var x) M' \<in> I A" by (rule Env.IH[OF xa sn cbv_VarR[OF Env.prems(1)] c])
    moreover have "App M' N \<in> I A" if "N \<in> I (QN x)" for N
      by (rule Env.IH[OF xa sn cbv_AppL[OF Env.prems(1)] a[OF that]])
    ultimately show ?thesis by blast
  qed
  then show ?case using Env.prems CFN_fwd by (simp add: I_Env)
qed

lemma I_fwd_steps: "M \<rightarrow>\<^sub>v\<^sup>* M' \<Longrightarrow> M \<in> I A \<Longrightarrow> M' \<in> I A"
  by (induction rule: rtranclp_induct) (auto intro: I_fwd)

lemma I_ess: "ess A \<Longrightarrow> M \<in> I A \<Longrightarrow> CFN M"
proof (induction A arbitrary: M)
  case (TV n) then show ?case by simp
next
  case Om then show ?case by simp
next
  case (Arr A B) then show ?case by simp
next
  case (Inter A B)
  then show ?case by (cases "ess A") simp_all
next
  case (QN x) then show ?case using CFN_QN by simp
next
  case (Env m ob)
  then show ?case by (simp add: I_Env)
qed

lemma wneu_I: "qfree A \<Longrightarrow> wneu M \<Longrightarrow> M \<in> I A"
proof (induction A arbitrary: M)
  case (TV n) then show ?case using wneu_CFN by simp
next
  case Om then show ?case by simp
next
  case (Arr A B)
  then show ?case using wneu_CFN wneu.intros(2) by simp
next
  case (Inter A B) then show ?case by simp
next
  case (QN x) then show ?case by simp
next
  case (Env m ob)
  have "Comp (Var x) M \<in> I A \<and> (\<forall>N \<in> I (QN x). App M N \<in> I A)" if l: "map_of m x = Some A" for x A
  proof -
    have xa: "(x, A) \<in> set m" using l by (rule map_of_SomeD)
    have sn: "A \<in> Basic_BNFs.snds (x, A)" by simp
    have q: "qfree A" using Env.prems(1) xa by force
    have w: "wneu (Comp (Var x) M)" using Env.prems(2) by (rule wneu.intros(3))
    have "Comp (Var x) M \<in> I A" by (rule Env.IH[OF xa sn q w])
    moreover have "App M N \<in> I A" if "N \<in> I (QN x)" for N
      by (rule Env.IH[OF xa sn q wneu.intros(2)[OF Env.prems(2) CFN_QN]]) (use that in \<open>simp add: I_QN\<close>)
    ultimately show ?thesis by blast
  qed
  then show ?case using Env.prems wneu_CFN by (simp add: I_Env)
qed

lemma Var_I: "qfree A \<Longrightarrow> Var x \<in> I A"
  by (rule wneu_I[OF _ wneu.intros(1)])

subsection \<open>Monotonicity\<close>

lemma I_mono: "A \<preceq> B \<Longrightarrow> I A \<subseteq> I B"
proof (induction rule: sub.induct)
  case (s_arr A' A B B')
  then show ?case by auto
next
  case (s_env m' m ob' ob)
  show ?case
  proof
    fix e
    assume e: "e \<in> I (Env m ob)"
    have cf: "CFN e" if "m' \<noteq> [] \<or> ob'"
    proof -
      have "m \<noteq> [] \<or> ob"
      proof (cases "m' = []")
        case True then show ?thesis using that s_env.hyps by auto
      next
        case False
        then obtain p ps where "m' = p # ps" by (cases m') auto
        then have "map_of m' (fst p) = Some (snd p)" by (cases p) simp
        then obtain A where "map_of m (fst p) = Some A" using s_env.IH by blast
        then show ?thesis by auto
      qed
      then show ?thesis using e by (simp add: I_Env)
    qed
    moreover have "Comp (Var x) e \<in> I A' \<and> (\<forall>N \<in> I (QN x). App e N \<in> I A')"
      if l: "map_of m' x = Some A'" for x A'
    proof -
      obtain A where "map_of m x = Some A" and "I A \<subseteq> I A'"
        using s_env.IH l by blast
      then show ?thesis using e by (auto simp: I_Env)
    qed
    ultimately show "e \<in> I (Env m' ob')" by (simp add: I_Env)
  qed
next
  case (s_emeet m1 o1 m2 o2)
  show ?case
  proof
    fix e
    assume "e \<in> I (Inter (Env m1 o1) (Env m2 o2))"
    then have e1: "e \<in> I (Env m1 o1)" and e2: "e \<in> I (Env m2 o2)" by simp_all
    have cf: "CFN e" if "emeet m1 m2 \<noteq> [] \<or> o1 \<or> o2"
      using that e1 e2 by (auto simp: I_Env emeet_def)
    moreover have "Comp (Var x) e \<in> I A \<and> (\<forall>N \<in> I (QN x). App e N \<in> I A)"
      if l: "map_of (emeet m1 m2) x = Some A" for x A
    proof (cases "map_of m1 x")
      case None
      then have "map_of m2 x = Some A" using l by (simp add: map_of_emeet)
      then show ?thesis using e2 by (simp add: I_Env)
    next
      case (Some A1)
      show ?thesis
      proof (cases "map_of m2 x")
        case None
        then have "A = A1" using l Some by (simp add: map_of_emeet)
        then show ?thesis using e1 Some by (simp add: I_Env)
      next
        case (Some A2)
        then have "A = Inter A1 A2" using l \<open>map_of m1 x = Some A1\<close> by (simp add: map_of_emeet)
        then show ?thesis using e1 e2 Some \<open>map_of m1 x = Some A1\<close> by (auto simp: I_Env)
      qed
    qed
    ultimately show "e \<in> I (Env (emeet m1 m2) (o1 \<or> o2))" by (simp add: I_Env)
  qed
next
  case s_omenv
  then show ?case by (auto simp: I_Env)
next
  case (s_envarr m x A ob)
  show ?case
  proof
    fix e
    assume e: "e \<in> I (Env m ob)"
    have "CFN e" using e s_envarr by (auto simp: I_Env)
    moreover have "App e N \<in> I A" if "N \<in> I (QN x)" for N
      using e s_envarr that by (auto simp: I_Env)
    ultimately show "e \<in> I (Arr (QN x) A)" by simp
  qed
next
  case (s_arrenv x A)
  show ?case
  proof
    fix M
    assume "M \<in> I (Arr (QN x) A)"
    then have cf: "CFN M" and ap: "\<And>N. N \<in> I (QN x) \<Longrightarrow> CFN N \<Longrightarrow> App M N \<in> I A" by simp_all
    have ap': "\<And>N. N \<in> I (QN x) \<Longrightarrow> App M N \<in> I A" using ap CFN_QN by (simp add: I_QN)
    have "App M (Nm x) \<in> I A" by (rule ap') (simp add: I_QN)
    then have "Comp (Var x) M \<in> I A" using I_fwd[OF cbv_AppConst] by blast
    then show "M \<in> I (Env [(x, A)] False)" using cf ap' by (simp add: I_Env)
  qed
qed auto

subsection \<open>Realizers\<close>

lemma Id_I:
  assumes q: "\<forall>p \<in> set m. qfree (snd p)"
  shows "Id \<in> I (Env m ob)"
proof -
  have "CFN Id" by (rule CFN_Id)
  moreover have "Comp (Var x) Id \<in> I A \<and> (\<forall>N \<in> I (QN x). App Id N \<in> I A)"
    if l: "map_of m x = Some A" for x A
  proof -
    have qa: "qfree A" using q map_of_SomeD[OF l] by force
    have c: "Comp (Var x) Id \<in> I A"
      using I_back[OF sig_imp_cbv[OF sig.IdR] Var_I[OF qa]] .
    have "App Id N \<in> I A" if n: "N \<in> I (QN x)" for N
    proof -
      have "App Id N \<rightarrow>\<^sub>v\<^sup>* App Id (Nm x)" using n by (simp add: I_QN cbv_steps_AppR[OF FId])
      moreover have "App Id (Nm x) \<in> I A" using I_back[OF cbv_AppConst c] .
      ultimately show ?thesis by (rule I_back_steps)
    qed
    with c show ?thesis by blast
  qed
  ultimately show ?thesis by (simp add: I_Env)
qed

lemma Extn_I:
  assumes n: "N \<in> I A" and e: "e \<in> I (Env m ob)"
  shows "Extn N x e \<in> I (Env ((x, A) # m) ob)"
proof -
  have "Comp (Var y) (Extn N x e) \<in> I B \<and> (\<forall>N' \<in> I (QN y). App (Extn N x e) N' \<in> I B)"
    if l: "map_of ((x, A) # m) y = Some B" for y B
  proof -
    have c: "Comp (Var y) (Extn N x e) \<in> I B"
    proof (cases "y = x")
      case True
      then have "B = A" using l by simp
      then show ?thesis using True I_back[OF sig_imp_cbv[OF sig.VarRef] n] by simp
    next
      case False
      then have "map_of m y = Some B" using l by simp
      then have "Comp (Var y) e \<in> I B" using e by (simp add: I_Env)
      moreover have "Comp (Var y) (Extn N x e) \<rightarrow>\<^sub>v Comp (Var y) e"
        using False by (simp add: sig_imp_cbv sig.VarSkip)
      ultimately show ?thesis using I_back by blast
    qed
    have "App (Extn N x e) N' \<in> I B" if n': "N' \<in> I (QN y)" for N'
    proof -
      have "App (Extn N x e) N' \<rightarrow>\<^sub>v\<^sup>* App (Extn N x e) (Nm y)"
        using n' by (simp add: I_QN cbv_steps_AppR[OF FExtn])
      moreover have "App (Extn N x e) (Nm y) \<in> I B" using I_back[OF cbv_AppConst c] .
      ultimately show ?thesis by (rule I_back_steps)
    qed
    with c show ?thesis by blast
  qed
  then show ?thesis using CFN_Extn by (simp add: I_Env)
qed

subsection \<open>Basic lemma\<close>

definition env_app :: "trm \<Rightarrow> trm \<Rightarrow> trm" where
  "env_app M e = (if e = Id then M else Comp M e)"

lemma basic: "C \<turnstile> M : A \<Longrightarrow> e \<in> I C \<Longrightarrow> env_app M e \<in> I A"
proof (induction arbitrary: e rule: hasty.induct)
  case (TVar C m ob x A)
  have em: "e \<in> I (Env m ob)" using I_mono[OF TVar.hyps(1)] TVar.prems by blast
  then have c: "Comp (Var x) e \<in> I A" using TVar.hyps(2) by (simp add: I_Env)
  show ?case
  proof (cases "e = Id")
    case True
    then have "Comp (Var x) Id \<in> I A" using c by simp
    then show ?thesis using True I_fwd[OF sig_imp_cbv[OF sig.IdR]] by (simp add: env_app_def)
  next
    case False then show ?thesis using c by (simp add: env_app_def)
  qed
next
  case (TLam C m ob x A M B)
  have em: "e \<in> I (Env m ob)" using I_mono[OF TLam.hyps(1)] TLam.prems by blast
  have fl: "fb (env_app (Lam x M) e)" by (simp add: env_app_def FLam FClo)
  have app: "App (env_app (Lam x M) e) N \<in> I B" if n: "N \<in> I A" and cn: "CFN N" for N
  proof -
    from cn obtain F where r: "N \<rightarrow>\<^sub>v\<^sup>* F" and f: "fb F" by (auto simp: CFN_def)
    have nF: "F \<in> I A" by (rule I_fwd_steps[OF r n])
    have "App (env_app (Lam x M) e) F \<in> I B"
    proof (cases "e = Id")
      case True
      have "Extn F x Id \<in> I (Env ((x, A) # m) ob)" using True em by (blast intro: Extn_I[OF nF])
      then have "Comp M (Extn F x Id) \<in> I B" using TLam.IH by (force simp: env_app_def)
      then show ?thesis using True I_back[OF beta_imp_cbv[OF beta.Beta2[OF f]]]
        by (simp add: env_app_def)
    next
      case False
      have "Extn F x e \<in> I (Env ((x, A) # m) ob)" by (rule Extn_I[OF nF em])
      then have "Comp M (Extn F x e) \<in> I B" using TLam.IH by (force simp: env_app_def)
      then show ?thesis using False I_back[OF beta_imp_cbv[OF beta.Beta1[OF f]]]
        by (simp add: env_app_def)
    qed
    then show ?thesis using I_back_steps[OF cbv_steps_AppR[OF fl r]] by blast
  qed
  have "CFN (env_app (Lam x M) e)"
    by (simp add: env_app_def CFN_Lam CFN_Clo)
  with app show ?case by simp
next
  case (TApp C M A B N)
  have m: "env_app M e \<in> I (Arr A B)" and n: "env_app N e \<in> I A"
    using TApp.IH TApp.prems by blast+
  have cn: "CFN (env_app N e)" by (rule I_ess[OF TApp.hyps(3) n])
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis using m n cn by (simp add: env_app_def)
  next
    case False
    have "App (Comp M e) (Comp N e) \<in> I B" using m n cn False by (simp add: env_app_def)
    then show ?thesis using False I_back[OF sig_imp_cbv[OF sig.DApp]] by (simp add: env_app_def)
  qed
next
  case (TId C)
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis using TId.prems by (simp add: env_app_def)
  next
    case False
    then show ?thesis using TId.prems I_back[OF sig_imp_cbv[OF sig.IdL]] by (simp add: env_app_def)
  qed
next
  case (TExtn C M A N m ob x)
  have m: "env_app M e \<in> I A" and n: "env_app N e \<in> I (Env m ob)"
    using TExtn.IH TExtn.prems by blast+
  have r: "Extn (env_app M e) x (env_app N e) \<in> I (Env ((x, A) # m) ob)"
    by (rule Extn_I[OF m n])
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis using r by (simp add: env_app_def)
  next
    case False
    then show ?thesis using r I_back[OF sig_imp_cbv[OF sig.DExtn]] by (simp add: env_app_def)
  qed
next
  case (TComp C N D M A)
  show ?case
  proof (cases "e = Id")
    case True
    have n: "N \<in> I D" using TComp.IH(1)[OF TComp.prems] True by (simp add: env_app_def)
    have "env_app M N \<in> I A" using TComp.IH(2)[OF n] .
    then show ?thesis
      using True I_back[OF sig_imp_cbv[OF sig.IdR]] by (cases "N = Id") (simp_all add: env_app_def)
  next
    case False
    have n: "Comp N e \<in> I D" using TComp.IH(1)[OF TComp.prems] False by (simp add: env_app_def)
    have "env_app M (Comp N e) \<in> I A" using TComp.IH(2)[OF n] .
    then have "Comp M (Comp N e) \<in> I A" by (simp add: env_app_def)
    then show ?thesis using False I_back[OF sig_imp_cbv[OF sig.Ass]] by (simp add: env_app_def)
  qed
next
  case (TNm C x)
  show ?case
  proof (cases "e = Id")
    case True then show ?thesis by (simp add: env_app_def I_QN)
  next
    case False
    have "Nm x \<in> I (QN x)" by (simp add: I_QN)
    then have "Comp (Nm x) e \<in> I (QN x)"
      by (rule I_back[OF sig_imp_cbv[OF sig.ConstComp]])
    then show ?thesis using False by (simp add: env_app_def)
  qed
next
  case (TOm C M)
  then show ?case by simp
next
  case (TInter C M A B)
  then show ?case by simp
next
  case (TSub C M A B)
  then show ?case using I_mono by blast
qed

theorem soundness: "Typ M \<Longrightarrow> CFN M"
proof -
  assume "Typ M"
  then obtain m ob A where t: "Env m ob \<turnstile> M : A" and e: "ess A"
    and q: "\<forall>p \<in> set m. qfree (snd p)" by (auto simp: Typ_def)
  have "env_app M Id \<in> I A" by (rule basic[OF t Id_I[OF q]])
  then have "M \<in> I A" by (simp add: env_app_def)
  then show "CFN M" by (rule I_ess[OF e])
qed

end
