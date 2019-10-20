theory ReoAutomata
  imports Main
begin

section "Guarded strings"

type_synonym '\<Sigma> guard = "'\<Sigma> set"
type_synonym '\<Sigma> firings = "'\<Sigma> set"
type_synonym '\<Sigma> guarded_string = "('\<Sigma> guard \<times> '\<Sigma> firings) list"

section "Guarded automata"

record ('\<Sigma>,'Q) transition =
  source :: 'Q
  guard :: "'\<Sigma> guard"
  firings :: "'\<Sigma> firings"
  target :: 'Q

abbreviation step :: "'Q \<Rightarrow> '\<Sigma> guard \<Rightarrow> '\<Sigma> firings \<Rightarrow> 'Q \<Rightarrow> ('\<Sigma>, 'Q) transition" ("_ _\<rightarrow>_ _" [100, 100, 100, 100]) where
  "q g\<rightarrow>f q' \<equiv> \<lparr> source = q, guard = g, firings = f, target = q' \<rparr>"

record ('\<Sigma>, 'Q) guarded_automaton =
  ports :: "'\<Sigma> set"
  states :: "'Q set"
  transitions :: "('\<Sigma>,'Q) transition set"

definition wf_guarded_automaton :: "('\<Sigma>,'Q) guarded_automaton \<Rightarrow> bool" where
  "wf_guarded_automaton \<A> = (finite (ports \<A>) \<and> finite (states \<A>) \<and> source ` transitions \<A> \<subseteq> states \<A>
    \<and> \<Union>(guard ` transitions \<A>) \<subseteq> ports \<A> \<and> \<Union>(firings ` transitions \<A>) \<subseteq> ports \<A>
    \<and> target ` transitions \<A> \<subseteq> states \<A> \<and> states \<A> \<noteq> {})"

lemma wf_guarded_automatonI [intro!]:
  "\<lbrakk> finite (ports \<A>); finite (states \<A>); source ` transitions \<A> \<subseteq> states \<A>;
     \<Union>(guard ` transitions \<A>) \<subseteq> ports \<A>; \<Union>(firings ` transitions \<A>) \<subseteq> ports \<A>;
     target ` transitions \<A> \<subseteq> states \<A>; states \<A> \<noteq> {} \<rbrakk> \<Longrightarrow> wf_guarded_automaton \<A>"
  by (auto simp add: wf_guarded_automaton_def)

abbreviation neutral_automaton :: "'Q \<Rightarrow> ('\<Sigma>,'Q) guarded_automaton" ("1\<^sub>\<A>") where
  "1\<^sub>\<A> x \<equiv> \<lparr>ports = {}, states = {x}, transitions = {}\<rparr>"

lemma wf_guarded_automaton_has_model:
  "wf_guarded_automaton (neutral_automaton x)"
  by auto

lemma wf_implies_wf_transitions [intro, dest, consumes 2]:
  assumes 
    "wf_guarded_automaton \<A>" and
    "q g\<rightarrow>f q' \<in> transitions \<A>"
  shows
    "q \<in> states \<A>"
    "g \<subseteq> ports \<A>"
    "f \<subseteq> ports \<A>"
    "q' \<in> states \<A>"
  using assms wf_guarded_automaton_def by fastforce+

inductive accepts :: "('\<Sigma>, 'Q) guarded_automaton \<Rightarrow> 'Q \<Rightarrow> '\<Sigma> guarded_string \<Rightarrow> bool" where
  empty: "q \<in> states \<A> \<Longrightarrow> accepts \<A> q []"
| step: "\<lbrakk> q \<in> states \<A>; q g\<rightarrow>f q' \<in> transitions \<A>; accepts \<A> q' tail \<rbrakk> \<Longrightarrow> accepts \<A> q ((g, f) # tail)"

abbreviation sync :: "'\<Sigma> \<Rightarrow> '\<Sigma> \<Rightarrow> 'Q \<Rightarrow> ('\<Sigma>, 'Q) guarded_automaton" where
  "sync a b q \<equiv> \<lparr> ports = {a, b}, states = {q}, transitions = { q {a,b}\<rightarrow>{a,b} q } \<rparr>"

lemma "accepts (sync a b q) q ([({a,b}, {a,b}), ({a,b}, {a,b})])" 
  by (auto intro!: accepts.intros)

lemma "a \<noteq> b \<Longrightarrow> \<not> (accepts (sync a b q) q ([({a,b}, {a,b}), ({a}, {a,b})]))"
  by (auto elim!: accepts.cases)

definition language :: "('\<Sigma>, 'Q) guarded_automaton \<Rightarrow> 'Q \<Rightarrow> '\<Sigma> guarded_string set" where
  "language \<A> q = { s |s.  accepts \<A> q s }"

lemma language_nonempty: "q \<in> states \<A> \<Longrightarrow> language \<A> q \<noteq> {}"
  using empty language_def by fastforce

definition prefix_closed :: "'a list set \<Rightarrow> bool" where
  "prefix_closed L = (\<forall>v w. (v @ w) \<in> L \<longrightarrow> v \<in> L)"

lemma accepts_butlast:
  assumes
    q_in_\<A>: "q \<in> states \<A>" and
    accepts_tail: "accepts \<A> q xs"
  shows "accepts \<A> q (butlast xs)"
proof (use assms in \<open>induct xs arbitrary: q\<close>)
  case Nil
  thus ?case by simp
next
  case (Cons rqs_fs tl)
  obtain rqs fs where hd: "rqs_fs = (rqs, fs)" by (cases rqs_fs) simp
  obtain q' where "q' \<in> states \<A>" and "q rqs\<rightarrow>fs q' \<in> transitions \<A>" and "accepts \<A> q' tl"
    by (use Cons.prems(2) in cases) (metis Pair_inject accepts.cases hd)
  thus ?case using hd by (auto simp add: Cons.prems(1) empty accepts.step Cons.hyps)
qed

lemma language_prefix_closed: "prefix_closed (language \<A> q)" 
proof -
  have "\<And>v w. accepts \<A> q (v @ w) \<Longrightarrow> accepts \<A> q v"
  proof -
    fix v w
    assume accepts: "accepts \<A> q (v @ w)"
    obtain n where len: "length (v @ w) = n" by simp
    show "accepts \<A> q v"
    proof (use accepts len in \<open>induct n arbitrary: w\<close>)
      case 0
      then show ?case by simp
    next
      case Suc: (Suc n)
      have "accepts \<A> q (butlast (v @ w))" by (meson Suc.prems(1) accepts.cases accepts_butlast)
      hence "accepts \<A> q (v @ butlast w)" by (metis Suc.prems(1) butlast.simps(1) butlast_append)
      then show ?case
        by (metis (mono_tags) One_nat_def Suc.hyps Suc.prems(1-2) append_Nil2 butlast_append diff_Suc_Suc diff_zero length_butlast)
    qed
  qed
  thus ?thesis by (simp add: language_def prefix_closed_def)
qed

definition simulating where
  "simulating R \<A>\<^sub>1 \<A>\<^sub>2 = (\<forall>q\<^sub>1 q\<^sub>2. (q\<^sub>1,q\<^sub>2) \<in> R \<longrightarrow> 
    (\<forall>g f q\<^sub>1'. q\<^sub>1 g\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1 \<longrightarrow> (\<exists>q\<^sub>2'. q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<and> (q\<^sub>1',q\<^sub>2') \<in> R))
  \<and> (\<forall>g f q\<^sub>2'. q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<longrightarrow> (\<exists>q\<^sub>1'. q\<^sub>1 g\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1 \<and> (q\<^sub>1',q\<^sub>2') \<in> R)))"

lemma simulatingI [intro]:
"(\<And>q\<^sub>1 q\<^sub>2 g f q\<^sub>1' q\<^sub>2'. (q\<^sub>1,q\<^sub>2) \<in> R \<Longrightarrow> ((q\<^sub>1 g\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1 \<longrightarrow> (\<exists>q\<^sub>2'. q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<and> (q\<^sub>1',q\<^sub>2') \<in> R))
  \<and> (q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<longrightarrow> (\<exists>q\<^sub>1'. q\<^sub>1 g\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1 \<and> (q\<^sub>1',q\<^sub>2') \<in> R)))) \<Longrightarrow> simulating R \<A>\<^sub>1 \<A>\<^sub>2"
  by (auto simp add: simulating_def)

definition bisimulates :: "('Q\<^sub>1 \<times> 'Q\<^sub>2) set \<Rightarrow> ('\<Sigma>, 'Q\<^sub>1) guarded_automaton \<Rightarrow> ('\<Sigma>, 'Q\<^sub>2) guarded_automaton \<Rightarrow> bool" where 
  "bisimulates R \<A>\<^sub>1 \<A>\<^sub>2 = (ports \<A>\<^sub>1 = ports \<A>\<^sub>2 \<and> R \<subseteq> states \<A>\<^sub>1 \<times> states \<A>\<^sub>2 \<and> states \<A>\<^sub>1 \<subseteq> fst ` R \<and> states \<A>\<^sub>2 \<subseteq> snd ` R \<and> simulating R \<A>\<^sub>1 \<A>\<^sub>2)"

lemma bisimulatesI [intro!]:
  "\<lbrakk> ports \<A>\<^sub>1 = ports \<A>\<^sub>2; R \<subseteq> states \<A>\<^sub>1 \<times> states \<A>\<^sub>2; states \<A>\<^sub>1 \<subseteq> fst ` R; states \<A>\<^sub>2 \<subseteq> snd ` R; simulating R \<A>\<^sub>1 \<A>\<^sub>2 \<rbrakk>
  \<Longrightarrow> bisimulates R \<A>\<^sub>1 \<A>\<^sub>2"
  by (auto simp add: bisimulates_def)

definition bisimilar :: "('\<Sigma>, 'Q\<^sub>1) guarded_automaton \<Rightarrow> ('\<Sigma>, 'Q\<^sub>2) guarded_automaton \<Rightarrow> bool" ("_ \<sim> _" [100,100]) where
  "bisimilar \<A>\<^sub>1 \<A>\<^sub>2 = (\<exists>R. bisimulates R \<A>\<^sub>1 \<A>\<^sub>2)"

lemma bisim_refl: "wf_guarded_automaton \<A> \<Longrightarrow> \<A> \<sim> \<A>"
proof -
  assume wf: "wf_guarded_automaton \<A>"
  let ?R = "{ (q,q) |q. q \<in> states \<A> }"
  have "bisimulates ?R \<A> \<A>" using wf by (auto simp add: image_iff)
  thus ?thesis using bisimilar_def by blast
qed

lemma fst_conv_R_snd_R [simp]: "fst ` R\<inverse> = snd ` R" by (simp add: Range_snd fst_eq_Domain)
lemma snd_conv_R_fst_R [simp]: "snd ` R\<inverse> = fst ` R" by (simp add: Domain_fst snd_eq_Range)

lemma bisim_sym [intro]: "\<A>\<^sub>1 \<sim> \<A>\<^sub>2 \<Longrightarrow> \<A>\<^sub>2 \<sim> \<A>\<^sub>1"
proof -
  assume "\<A>\<^sub>1 \<sim> \<A>\<^sub>2"
  then obtain R where R_bisim: "bisimulates R \<A>\<^sub>1 \<A>\<^sub>2" using bisimilar_def by blast
  have "bisimulates (R\<inverse>) \<A>\<^sub>2 \<A>\<^sub>1" using R_bisim by (auto simp add: simulating_def bisimulates_def)
  thus ?thesis using bisimilar_def by blast
qed

lemma simulating_trans: "simulating R \<A>\<^sub>1 \<A>\<^sub>2 \<Longrightarrow> simulating R' \<A>\<^sub>2 \<A>\<^sub>3 \<Longrightarrow> simulating (R O R') \<A>\<^sub>1 \<A>\<^sub>3"
  by (auto simp add: simulating_def, (meson relcomp.relcompI)+)

lemma boo1 [simp]: "snd ` R = fst ` R' \<Longrightarrow> fst ` (R O R') = fst ` R"
  by (auto simp add: image_iff, force+)
lemma boo2 [simp]: "snd ` R = fst ` R' \<Longrightarrow> snd ` (R O R') = snd ` R'" 
  by (auto simp add: image_iff, force+)

lemma bisim_trans [intro]: "\<A>\<^sub>1 \<sim> \<A>\<^sub>2 \<Longrightarrow> \<A>\<^sub>2 \<sim> \<A>\<^sub>3 \<Longrightarrow> \<A>\<^sub>1 \<sim> \<A>\<^sub>3"
proof -
  assume sim1: "\<A>\<^sub>1 \<sim> \<A>\<^sub>2" and sim2: "\<A>\<^sub>2 \<sim> \<A>\<^sub>3"
  from sim1 obtain R where R_bisim: "bisimulates R \<A>\<^sub>1 \<A>\<^sub>2" using bisimilar_def by blast
  from sim2 obtain R' where R'_bisim: "bisimulates R' \<A>\<^sub>2 \<A>\<^sub>3" using bisimilar_def by blast
  have snd_eq_fst: "snd ` R = fst ` R'" using R_bisim R'_bisim by (auto 5 3 simp add: bisimilar_def bisimulates_def)
  have "bisimulates (R O R') \<A>\<^sub>1 \<A>\<^sub>3" using R_bisim R'_bisim snd_eq_fst by (auto simp add: bisimulates_def simulating_trans)
  thus ?thesis using bisimilar_def by auto
qed

abbreviation verbose_sync :: "'\<Sigma> \<Rightarrow> '\<Sigma> \<Rightarrow> 'Q \<Rightarrow> 'Q \<Rightarrow> ('\<Sigma>, 'Q) guarded_automaton" where
  "verbose_sync a b q\<^sub>1 q\<^sub>2 \<equiv> \<lparr> ports = {a,b}, states = {q\<^sub>1,q\<^sub>2}, transitions = { q\<^sub>1 {a,b}\<rightarrow>{a,b} q\<^sub>1, q\<^sub>1 {a,b}\<rightarrow>{a,b} q\<^sub>2, q\<^sub>2 {a,b}\<rightarrow>{a,b} q\<^sub>2 } \<rparr>"

abbreviation lossy_sync :: "'\<Sigma> \<Rightarrow> '\<Sigma> \<Rightarrow> 'Q \<Rightarrow> ('\<Sigma>, 'Q) guarded_automaton" where
  "lossy_sync a b q \<equiv> \<lparr> ports = {a,b}, states = {q}, transitions = { q {a,b}\<rightarrow>{a,b} q, q {a,b}\<rightarrow>{a} q, q {a}\<rightarrow>{a} q } \<rparr>"

proposition sync_and_verbose_sync_bisim: "(sync a b q) \<sim> (verbose_sync a b q\<^sub>1 q\<^sub>2)"
proof -
  have "bisimulates {(q,q\<^sub>1), (q,q\<^sub>2)} (sync a b q) (verbose_sync a b q\<^sub>1 q\<^sub>2)" 
    by (auto simp add: simulating_def)
  thus ?thesis by (auto simp add: bisimilar_def)
qed

lemma in_left_iff_in_right [intro]: 
  assumes 
    "bisimulates R \<A>\<^sub>1 \<A>\<^sub>2" and
    "R = {(q,q')}"
  shows 
    "q' {a}\<rightarrow>{a} q' \<in> transitions \<A>\<^sub>2 \<Longrightarrow> q {a}\<rightarrow>{a} q \<in> transitions \<A>\<^sub>1"
    "q {a}\<rightarrow>{a} q \<in> transitions \<A>\<^sub>1 \<Longrightarrow> q' {a}\<rightarrow>{a} q' \<in> transitions \<A>\<^sub>2"
  using assms by(auto simp add: bisimulates_def simulating_def)

proposition sync_and_lossy_sync_not_bisim: "a \<noteq> b \<Longrightarrow> \<not> (sync a b q) \<sim> (lossy_sync a b q')"
proof (rule notI)
  assume neq: "a \<noteq> b" and bisim: "(sync a b q) \<sim> (lossy_sync a b q')"
  from bisim obtain R where R_bisim: "bisimulates R (sync a b q) (lossy_sync a b q')"
    using bisimilar_def by blast
  hence R_eq: "R = {(q,q')}" by (auto simp add: bisimulates_def)
  have "q {a}\<rightarrow>{a} q \<in> transitions (sync a b q)" 
    by (rule in_left_iff_in_right(1)[where R=R and \<A>\<^sub>2="lossy_sync a b q'" and q'=q']) (use R_bisim R_eq in auto)
  thus False using neq by auto
qed

theorem bisim_implies_language_equivalence:
  fixes
    \<A>\<^sub>1 :: "('\<Sigma>,'Q) guarded_automaton"
  assumes
    R_bisim: "bisimulates R \<A>\<^sub>1 \<A>\<^sub>2" and
    states_bisim: "(q\<^sub>1,q\<^sub>2) \<in> R"
  shows "language \<A>\<^sub>1 q\<^sub>1 = language \<A>\<^sub>2 q\<^sub>2"
proof -
  have q\<^sub>1\<A>\<^sub>1: "q\<^sub>1 \<in> states \<A>\<^sub>1" using states_bisim R_bisim by (auto simp add: bisimulates_def)
  have q\<^sub>2\<A>\<^sub>2: "q\<^sub>2 \<in> states \<A>\<^sub>2" using states_bisim R_bisim by (auto simp add: bisimulates_def)
  have "\<And>w. (w \<in> language \<A>\<^sub>1 q\<^sub>1) = (w \<in> language \<A>\<^sub>2 q\<^sub>2)"
  proof -
    fix w :: "'\<Sigma> guarded_string"
    obtain n where len: "length w = n" by simp
    show "(w \<in> language \<A>\<^sub>1 q\<^sub>1) = (w \<in> language \<A>\<^sub>2 q\<^sub>2)"
    proof (use R_bisim states_bisim len q\<^sub>1\<A>\<^sub>1 q\<^sub>2\<A>\<^sub>2 in \<open>induct n arbitrary: w q\<^sub>1 q\<^sub>2\<close>)
      case zero: 0
      have w_empty: "w = []" using zero.prems by blast
      show ?case by (auto simp add: empty language_def q\<^sub>1\<A>\<^sub>1 q\<^sub>2\<A>\<^sub>2 w_empty zero.prems(4-5))
    next
      case suc: (Suc nat)
      obtain g f v where w_nonempty: "w = (g,f) # v" by (metis length_Suc_conv prod.collapse suc.prems(3))
      have len_v: "length v = nat" using w_nonempty suc.prems by auto
      show ?case
      proof (rule iffI)
        assume "w \<in> language \<A>\<^sub>1 q\<^sub>1"
        hence "accepts \<A>\<^sub>1 q\<^sub>1 w" by (simp add: language_def)
        then obtain q\<^sub>1' where 
          left_trans: "q\<^sub>1 g\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1" and 
          accepts_tail: "accepts \<A>\<^sub>1 q\<^sub>1' v"
          by cases (use w_nonempty in blast)+
        have "v \<in> language \<A>\<^sub>1 q\<^sub>1'" by (simp add: accepts_tail language_def)
        have "\<exists>q\<^sub>2'. q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<and> (q\<^sub>1', q\<^sub>2') \<in> R" 
          using states_bisim R_bisim left_trans suc.prems(2) by (auto simp add: bisimulates_def simulating_def)
        then obtain q\<^sub>2' where "q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2" and q\<^sub>1'q\<^sub>2': "(q\<^sub>1', q\<^sub>2') \<in> R" by blast
        have "accepts \<A>\<^sub>2 q\<^sub>2' v"
        proof -
          have q\<^sub>1'_in: "q\<^sub>1' \<in> states \<A>\<^sub>1" using accepts.cases accepts_tail by fastforce
          have q\<^sub>2'_in: "q\<^sub>2' \<in> states \<A>\<^sub>2" using R_bisim q\<^sub>1'q\<^sub>2' by (auto simp add: bisimulates_def)
          thus ?thesis using R_bisim language_def len_v q\<^sub>1'_in q\<^sub>1'q\<^sub>2' suc.hyps \<open>v \<in> language \<A>\<^sub>1 q\<^sub>1'\<close> q\<^sub>2'_in by force
        qed
        have "accepts \<A>\<^sub>2 q\<^sub>2 w"
          using \<open>accepts \<A>\<^sub>2 q\<^sub>2' v\<close> \<open>q\<^sub>2 g\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2\<close> accepts.step suc.prems(5) w_nonempty by fastforce
        thus "w \<in> language \<A>\<^sub>2 q\<^sub>2"  by (simp add: language_def)
      next
        show "w \<in> language \<A>\<^sub>2 q\<^sub>2 \<Longrightarrow> w \<in> language \<A>\<^sub>1 q\<^sub>1" sorry (* symmetric, but clean up first *)
      qed
    qed
  qed
  thus ?thesis by blast
qed

subsection Product

definition nonenabling :: "('\<Sigma>,'Q) guarded_automaton \<Rightarrow> 'Q \<Rightarrow> '\<Sigma> guard set" ("_ _\<^sup>#") where
  "\<A> q\<^sup># = Pow (ports \<A>) - {g |g. \<exists>f q'. q g\<rightarrow>f q' \<in> transitions \<A>}"

(*
definition nonenabling :: "('\<Sigma>,'Q) guarded_automaton \<Rightarrow> 'Q \<Rightarrow> '\<Sigma> guard set" ("_ _\<^sup>#") where
  "\<A> q\<^sup># = Pow (ports \<A>) - (guard ` transitions \<A>)"

lemma transition_iff_not_nonenabling:
  "wf_guarded_automaton \<A> \<Longrightarrow> (g \<subseteq> ports \<A> \<and> g \<notin> (\<A> q\<^sup>#)) = (\<exists>t. t \<in> transitions \<A> \<and> guard t = g)"
  apply (auto simp add: nonenabling_def) sledgehammer
  by (metis old.unit.exhaust subsetCE transition.surjective wf_implies_wf_transitions(2))

lemma transition_if_not_nonenabling [intro]:
  assumes
    "g \<subseteq> ports \<A>" and
    "g \<notin> (\<A> q\<^sup>#)"
  shows "\<exists>q' f. q g\<rightarrow>f q' \<in> transitions \<A>" 
  using assms transition_iff_not_nonenabling by (auto simp add: nonenabling_def)
*)

lemma transition_iff_not_nonenabling:
  "wf_guarded_automaton \<A> \<Longrightarrow> (g \<subseteq> ports \<A> \<and> g \<notin> (\<A> q\<^sup>#)) = (\<exists>q' f. q g\<rightarrow>f q' \<in> transitions \<A>)"
  by (auto simp add: nonenabling_def)

lemma transition_if_not_nonenabling [intro]:
  assumes
    "g \<subseteq> ports \<A>" and
    "g \<notin> (\<A> q\<^sup>#)"
  shows "\<exists>q' f. q g\<rightarrow>f q' \<in> transitions \<A>" 
  using assms transition_iff_not_nonenabling by (auto simp add: nonenabling_def)

proposition "a \<noteq> b \<Longrightarrow> (sync a b q) q\<^sup># = {{},{a},{b}}" by (auto simp add: nonenabling_def)
proposition "a \<noteq> b \<Longrightarrow> (lossy_sync a b q) q\<^sup># = {{},{b}}" by (auto simp add: nonenabling_def)

abbreviation left_async where
  "left_async \<A>\<^sub>1 \<A>\<^sub>2 \<equiv> { (q,p) (g \<union> g')\<rightarrow>f (q',p) |q g f q' p g'.
  q g\<rightarrow>f q' \<in> transitions \<A>\<^sub>1 \<and> p \<in> states \<A>\<^sub>2 \<and> g' \<in> (\<A>\<^sub>2 p\<^sup>#) }"

abbreviation right_async where
  "right_async \<A>\<^sub>1 \<A>\<^sub>2 \<equiv> { (q,p) (g \<union> g')\<rightarrow>f (q,p') |p g f p' q g'.
  p g\<rightarrow>f p' \<in> transitions \<A>\<^sub>2 \<and> q \<in> states \<A>\<^sub>1 \<and> g' \<in> (\<A>\<^sub>1 q\<^sup>#) }"

abbreviation both_sync where
  "both_sync \<A>\<^sub>1 \<A>\<^sub>2 \<equiv> { (q,p) (g \<union> g')\<rightarrow>(f \<union> f') (q',p') |q g f q' p g' f' p'.
   q g\<rightarrow>f q' \<in> transitions \<A>\<^sub>1 \<and> p g'\<rightarrow>f' p' \<in> transitions \<A>\<^sub>2 }"

(* the product operation is defined under the assumption ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>2 = {} *)
fun product :: "('\<Sigma>,'Q\<^sub>1) guarded_automaton \<Rightarrow> ('\<Sigma>,'Q\<^sub>2) guarded_automaton \<Rightarrow> ('\<Sigma>,'Q\<^sub>1\<times>'Q\<^sub>2) guarded_automaton" ("_ \<times>\<^sub>\<A> _")  where
  "product \<A>\<^sub>1 \<A>\<^sub>2 = \<lparr> ports = ports \<A>\<^sub>1 \<union> ports \<A>\<^sub>2, states = states \<A>\<^sub>1 \<times> states \<A>\<^sub>2, 
    transitions = left_async \<A>\<^sub>1 \<A>\<^sub>2 \<union> right_async \<A>\<^sub>1 \<A>\<^sub>2 \<union> both_sync \<A>\<^sub>1 \<A>\<^sub>2 \<rparr>"

lemma prod_transitionE [elim, consumes 1, case_names left_async right_async both_sync]:
  assumes 
    prod_trans: "(q\<^sub>1,q\<^sub>2) g\<rightarrow>f (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" and
    left: "\<And>g\<^sub>1 g\<^sub>2. q\<^sub>2 = q\<^sub>2' \<Longrightarrow> g = g\<^sub>1 \<union> g\<^sub>2 \<Longrightarrow> q\<^sub>1 g\<^sub>1\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1 \<Longrightarrow> g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#) \<Longrightarrow> P" and
    right: "\<And>g\<^sub>1 g\<^sub>2. q\<^sub>1 = q\<^sub>1' \<Longrightarrow> g = g\<^sub>1 \<union> g\<^sub>2 \<Longrightarrow> q\<^sub>2 g\<^sub>2\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<Longrightarrow> g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#) \<Longrightarrow> P" and
    both: "\<And>g\<^sub>1 g\<^sub>2 f\<^sub>1 f\<^sub>2. g = g\<^sub>1 \<union> g\<^sub>2 \<Longrightarrow> f = f\<^sub>1 \<union> f\<^sub>2 \<Longrightarrow> q\<^sub>1 g\<^sub>1\<rightarrow>f\<^sub>1 q\<^sub>1' \<in> transitions \<A>\<^sub>1 \<Longrightarrow> q\<^sub>2 g\<^sub>2\<rightarrow>f\<^sub>2 q\<^sub>2' \<in> transitions \<A>\<^sub>2 \<Longrightarrow> P"
  shows "P"
  using assms by (auto 4 0)

lemma wf_invariant_product [intro]:
  assumes 
    \<A>\<^sub>1_GA: "wf_guarded_automaton \<A>\<^sub>1" and
    \<A>\<^sub>2_GA: "wf_guarded_automaton \<A>\<^sub>2"
  shows "wf_guarded_automaton (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
    using assms by (auto 0 0 simp add: wf_guarded_automaton_def, auto simp add: nonenabling_def)

lemma product_neutral_element:
  "wf_guarded_automaton \<A> \<Longrightarrow> \<A> \<sim> (\<A> \<times>\<^sub>\<A> (1\<^sub>\<A> x))" (is "_ \<Longrightarrow> _ \<sim> ?\<P>")
proof -
  assume wf_\<A>: "wf_guarded_automaton \<A>"
  let ?R = "{ (q,(q,x)) |q. q \<in> states \<A>}"
  have "bisimulates ?R \<A> ?\<P>"
  proof (rule bisimulatesI)
    show "simulating {(q,q,x) |q. q \<in> states \<A>} \<A> ?\<P>"
      by (rule simulatingI) (use wf_\<A> in \<open>auto simp add: nonenabling_def\<close>)
  qed (auto simp add: image_iff)
  thus ?thesis using bisimilar_def by blast
qed

lemma product_commutative:
  assumes 
    \<A>\<^sub>1_GA: "wf_guarded_automaton \<A>\<^sub>1" and
    \<A>\<^sub>2_GA: "wf_guarded_automaton \<A>\<^sub>2"
  shows "(\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) \<sim> (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>1)" (is "?l \<sim> ?r")
proof -
  let ?R = "{ ((q\<^sub>1,q\<^sub>2), (q\<^sub>2,q\<^sub>1)) |q\<^sub>1 q\<^sub>2. (q\<^sub>1,q\<^sub>2) \<in> states ?l }"
  have "bisimulates ?R ?l ?r"
  proof (rule bisimulatesI)
    show "simulating ?R ?l ?r" by (rule simulatingI) (use assms in \<open>auto 0 3 simp add: sup_commute\<close>)
  qed (auto simp add: image_iff)
  thus ?thesis using bisimilar_def by blast
qed

lemma nonenabling_components_nonenabling_product:
  assumes
    wf_\<A>\<^sub>1: "wf_guarded_automaton \<A>\<^sub>1" and
    wf_\<A>\<^sub>2: "wf_guarded_automaton \<A>\<^sub>2" and
    g\<^sub>1_blocks: "g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)" and
    g\<^sub>2_blocks: "g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)" and
    disjoint: "ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>2 = {}"
  shows "g\<^sub>1 \<union> g\<^sub>2 \<in> ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) (q\<^sub>1,q\<^sub>2)\<^sup>#)"
proof (rule ccontr)
  assume ass: "g\<^sub>1 \<union> g\<^sub>2 \<notin> ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) (q\<^sub>1, q\<^sub>2)\<^sup>#)"
  have "\<exists>q' f. (q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>f q' \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
    by (rule transition_if_not_nonenabling, use g\<^sub>1_blocks g\<^sub>2_blocks ass in \<open>auto simp add: nonenabling_def\<close>)
  then obtain q\<^sub>1' q\<^sub>2' f where "(q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>f (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" by force
  thus False
  proof (cases rule: prod_transitionE)
    case (left_async g\<^sub>1' g\<^sub>2')
    hence g\<^sub>1'_blocks: "g\<^sub>1' \<notin> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)" by (auto simp add: nonenabling_def)
    have "g\<^sub>1 = g\<^sub>1'"
    proof (rule set_eqI, rule iffI)
      fix x
      assume "x \<in> g\<^sub>1"
      thus "x \<in> g\<^sub>1'"
        by (metis (no_types, lifting) DiffE IntI Pow_iff Un_iff disjoint emptyE g\<^sub>1_blocks left_async(2) left_async(4) nonenabling_def subsetCE)
    next
      fix x
      assume "x \<in> g\<^sub>1'"
      thus "x \<in> g\<^sub>1" 
        using disjoint g\<^sub>2_blocks left_async(2) left_async(3) nonenabling_def wf_\<A>\<^sub>1 wf_implies_wf_transitions(2) by fastforce
    qed
    thus ?thesis using g\<^sub>1_blocks g\<^sub>1'_blocks by blast
  next
    case (right_async g\<^sub>1' g\<^sub>2')
    hence g\<^sub>2'_blocks: "g\<^sub>2' \<notin> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)" by (auto simp add: nonenabling_def)
    have "g\<^sub>2 = g\<^sub>2'"
    proof (rule set_eqI, rule iffI)
      fix x
      assume "x \<in> g\<^sub>2"
      thus "x \<in> g\<^sub>2'"
        by (metis (no_types, lifting) DiffE IntI Pow_iff Un_iff disjoint emptyE g\<^sub>2_blocks insert_subset mk_disjoint_insert nonenabling_def right_async(2) right_async(4))
    next
      fix x
      assume "x \<in> g\<^sub>2'"
      thus "x \<in> g\<^sub>2"
        by (metis (no_types, lifting) DiffE Pow_iff UnE disjoint disjoint_iff_not_equal g\<^sub>1_blocks nonenabling_def right_async(2) right_async(3) subsetCE sup_commute sup_ge1 wf_\<A>\<^sub>2 wf_implies_wf_transitions(2))
    qed
    thus ?thesis using g\<^sub>2_blocks g\<^sub>2'_blocks by blast
  next
    case (both_sync g\<^sub>1' g\<^sub>2' f\<^sub>1' f\<^sub>2')
    have g\<^sub>1_eq_g\<^sub>1': "g\<^sub>1 = g\<^sub>1'"
    proof (rule set_eqI, rule iffI)
      fix x
      assume "x \<in> g\<^sub>1"
      thus "x \<in> g\<^sub>1'"
        using both_sync(1) both_sync(4) disjoint g\<^sub>1_blocks wf_\<A>\<^sub>2 wf_implies_wf_transitions(2) nonenabling_def by fastforce
    next
      fix x
      assume "x \<in> g\<^sub>1'"
      thus "x \<in> g\<^sub>1"
        by (metis (no_types, lifting) DiffE Pow_iff UnE both_sync(1) both_sync(3) disjoint disjoint_iff_not_equal g\<^sub>2_blocks nonenabling_def subset_iff sup_ge1 wf_\<A>\<^sub>1 wf_implies_wf_transitions(2))
    qed
    have g\<^sub>2_eq_g\<^sub>2': "g\<^sub>2 = g\<^sub>2'" using both_sync(3) g\<^sub>1_blocks g\<^sub>1_eq_g\<^sub>1' by (auto simp add: nonenabling_def)
    show ?thesis using both_sync(4) g\<^sub>2_blocks g\<^sub>2_eq_g\<^sub>2' by (auto simp add: nonenabling_def)
  qed
qed

lemma prod_trans_leftI [intro]:
  assumes
    "g = left_guard \<union> right_guard" and
    "q\<^sub>1 left_guard\<rightarrow>f q\<^sub>1' \<in> transitions \<A>\<^sub>1" and
    "q\<^sub>2 \<in> states \<A>\<^sub>2" and
    "right_guard \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)" and
    "q\<^sub>2 = q\<^sub>2'"
  shows "(q\<^sub>1,q\<^sub>2) g\<rightarrow>f (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
  using assms by (auto simp add: nonenabling_def)

lemma prod_trans_rightI [intro]:
  assumes
    "g = left_guard \<union> right_guard" and
    "q\<^sub>2 right_guard\<rightarrow>f q\<^sub>2' \<in> transitions \<A>\<^sub>2" and
    "q\<^sub>1 \<in> states \<A>\<^sub>1" and
    "left_guard \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)" and
    "q\<^sub>1 = q\<^sub>1'"
  shows "(q\<^sub>1,q\<^sub>2) g\<rightarrow>f (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
  using assms by auto

lemma prod_trans_bothI [intro]:
  assumes
    "g = left_guard \<union> right_guard" and
    "f = left_firing \<union> right_firing" and
    "q\<^sub>1 left_guard\<rightarrow>left_firing q\<^sub>1' \<in> transitions \<A>\<^sub>1" and
    "q\<^sub>2 right_guard\<rightarrow>right_firing q\<^sub>2' \<in> transitions \<A>\<^sub>2"
  shows "(q\<^sub>1,q\<^sub>2) g\<rightarrow>f (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
  using assms by (auto 0 5)

lemma tup_in_states [intro!]: "q\<^sub>1 \<in> states \<A>\<^sub>1 \<Longrightarrow> q\<^sub>2 \<in> states \<A>\<^sub>2 \<Longrightarrow> (q\<^sub>1, q\<^sub>2) \<in> states (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
  by auto

lemma nonenabling_product_simp [simp]:
  assumes 
    wf_\<A>\<^sub>1: "wf_guarded_automaton \<A>\<^sub>1" and
    wf_\<A>\<^sub>2: "wf_guarded_automaton \<A>\<^sub>2" and
    q\<^sub>1_in: "q\<^sub>1 \<in> states \<A>\<^sub>1" and
    q\<^sub>2_in: "q\<^sub>2 \<in> states \<A>\<^sub>2" and
    disjoint: "ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>2 = {}"
  shows "((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) (q\<^sub>1,q\<^sub>2)\<^sup>#) = { g\<^sub>1 \<union> g\<^sub>2 |g\<^sub>1 g\<^sub>2. g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#) \<and> g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#) }" (is "?l = ?r")
proof (rule set_eqI, rule iffI)
  fix g
  assume g_in: "g \<in> ?l"
  have "g \<subseteq> ports (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" using g_in by (simp add: nonenabling_def)
  then obtain g\<^sub>1 g\<^sub>2 where g\<^sub>1_sub: "g\<^sub>1 \<subseteq> ports \<A>\<^sub>1" and g\<^sub>2_sub: "g\<^sub>2 \<subseteq> ports \<A>\<^sub>2" and g_eq: "g = g\<^sub>1 \<union> g\<^sub>2"
    using g_in apply auto
    by (metis inf.absorb_iff1 inf.cobounded2 inf_sup_distrib1)
  have g\<^sub>1_in: "g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)"
  proof (rule ccontr)
    assume "g\<^sub>1 \<notin> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)"
    then obtain f\<^sub>1 q\<^sub>1' where left_fires: "q\<^sub>1 g\<^sub>1\<rightarrow>f\<^sub>1 q\<^sub>1' \<in> transitions \<A>\<^sub>1" by (auto simp add: g\<^sub>1_sub nonenabling_def)
    show False
    proof (cases "g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)")
      case True
      have "(q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>f\<^sub>1 (q\<^sub>1',q\<^sub>2) \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" 
        using left_fires q\<^sub>2_in g\<^sub>2_sub True by auto
      hence "g\<^sub>1 \<union> g\<^sub>2 \<notin> ?l" by (meson transition_iff_not_nonenabling wf_\<A>\<^sub>1 wf_\<A>\<^sub>2 wf_invariant_product)
      thus ?thesis using g_eq g_in by blast
    next
      case False
      then obtain f\<^sub>2 q\<^sub>2' where right_fires: "q\<^sub>2 g\<^sub>2\<rightarrow>f\<^sub>2 q\<^sub>2' \<in> transitions \<A>\<^sub>2" by (auto simp add: g\<^sub>2_sub nonenabling_def)
      hence "(q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>(f\<^sub>1 \<union> f\<^sub>2) (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
        using left_fires by blast
      hence "g\<^sub>1 \<union> g\<^sub>2 \<notin> ?l" by (meson transition_iff_not_nonenabling wf_\<A>\<^sub>1 wf_\<A>\<^sub>2 wf_invariant_product)
      thus ?thesis using g_eq g_in by blast
    qed
  qed
  have g\<^sub>2_in: "g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)"
  proof (rule ccontr)
    assume "g\<^sub>2 \<notin> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)"
    then obtain f\<^sub>2 q\<^sub>2' where right_fires: "q\<^sub>2 g\<^sub>2\<rightarrow>f\<^sub>2 q\<^sub>2' \<in> transitions \<A>\<^sub>2" by (auto simp add: g\<^sub>2_sub nonenabling_def)
    hence "(q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>f\<^sub>2 (q\<^sub>1,q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" using g\<^sub>1_in q\<^sub>1_in by blast
    hence "g\<^sub>1 \<union> g\<^sub>2 \<notin> ?l" by (meson transition_iff_not_nonenabling wf_\<A>\<^sub>1 wf_\<A>\<^sub>2 wf_invariant_product)
    thus False using g_eq g_in by blast
  qed
  show "g \<in> ?r" using g\<^sub>1_in g\<^sub>2_in g_eq by blast
next
  fix g
  assume "g \<in> ?r"
  then obtain g\<^sub>1 g\<^sub>2 where g\<^sub>1_in: "g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)" and g\<^sub>2_in: "g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)" and g_eq: "g = g\<^sub>1 \<union> g\<^sub>2"
    by blast
  thus "g \<in> ?l" by (meson disjoint nonenabling_components_nonenabling_product wf_\<A>\<^sub>1 wf_\<A>\<^sub>2)
qed

(*
lemma in_component_in_product [intro]:
  assumes 
    \<A>\<^sub>1_step: "q\<^sub>1 g\<^sub>1\<rightarrow>f\<^sub>1 q\<^sub>1' \<in> transitions \<A>\<^sub>1" and
    wf_\<A>\<^sub>2: "wf_guarded_automaton \<A>\<^sub>2"
  shows "\<exists>q\<^sub>2 g\<^sub>2 f\<^sub>2 q\<^sub>2'. (q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>(f\<^sub>1 \<union> f\<^sub>2) (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
proof (cases "(transitions \<A>\<^sub>2) = {}")
  case True
  obtain q\<^sub>2 where q\<^sub>2_in: "q\<^sub>2 \<in> states \<A>\<^sub>2" by (meson ex_in_conv wf_\<A>\<^sub>2 wf_guarded_automaton_def)
  have "{} \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)" by (simp add: True nonenabling_def)
  hence "(q\<^sub>1,q\<^sub>2) (g\<^sub>1 \<union> {})\<rightarrow>(f\<^sub>1 \<union> {}) (q\<^sub>1',q\<^sub>2) \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
    using q\<^sub>2_in \<A>\<^sub>1_step by (auto simp add: nonenabling_def)
  then show ?thesis by blast
next
  case False
  obtain q\<^sub>2 g\<^sub>2 f\<^sub>2 q\<^sub>2' where "q\<^sub>2 g\<^sub>2\<rightarrow>f\<^sub>2 q\<^sub>2' \<in> transitions \<A>\<^sub>2" by (metis False equals0I transition.cases)
  then show ?thesis by (meson \<A>\<^sub>1_step prod_trans_bothI)
qed
*)

lemma nonenabling_product_components [intro]:
  assumes 
    wf_\<A>\<^sub>1: "wf_guarded_automaton \<A>\<^sub>1" and 
    wf_\<A>\<^sub>2: "wf_guarded_automaton \<A>\<^sub>2" and
    q\<^sub>1_in: "q\<^sub>1 \<in> states \<A>\<^sub>1" and
    q\<^sub>2_in: "q\<^sub>2 \<in> states \<A>\<^sub>2" and
    g_in: "g \<in> ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) (q\<^sub>1,q\<^sub>2)\<^sup>#)" and
    disjoint: "ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>2 = {}"
  shows
    "\<exists>g\<^sub>1 g\<^sub>2. g = g\<^sub>1 \<union> g\<^sub>2 \<and> g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#) \<and> g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)"
proof -
  have "((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) (q\<^sub>1,q\<^sub>2)\<^sup>#) = { g\<^sub>1 \<union> g\<^sub>2 |g\<^sub>1 g\<^sub>2. g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#) \<and> g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#) }" 
    by (rule nonenabling_product_simp[OF wf_\<A>\<^sub>1 wf_\<A>\<^sub>2 q\<^sub>1_in q\<^sub>2_in disjoint])
  thus ?thesis using g_in by blast
qed

lemma product_associative:
  assumes 
    \<A>\<^sub>1_GA: "wf_guarded_automaton \<A>\<^sub>1" and
    \<A>\<^sub>2_GA: "wf_guarded_automaton \<A>\<^sub>2" and
    \<A>\<^sub>3_GA: "wf_guarded_automaton \<A>\<^sub>3" and
    \<A>\<^sub>1_\<A>\<^sub>2_disjoint: "ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>2 = {}" and
    \<A>\<^sub>2_\<A>\<^sub>3_disjoint: "ports \<A>\<^sub>2 \<inter> ports \<A>\<^sub>3 = {}" and
    \<A>\<^sub>1_\<A>\<^sub>3_disjoint: "ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>3 = {}"
  shows "((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) \<times>\<^sub>\<A> \<A>\<^sub>3) \<sim> (\<A>\<^sub>1 \<times>\<^sub>\<A> (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3))" (is "?l \<sim> ?r")
proof -
  let ?R = "{ (((q\<^sub>1,q\<^sub>2),q\<^sub>3), (q\<^sub>1,(q\<^sub>2,q\<^sub>3))) |q\<^sub>1 q\<^sub>2 q\<^sub>3. ((q\<^sub>1,q\<^sub>2),q\<^sub>3) \<in> states ?l }"
  have R_bisim: "bisimulates ?R ?l ?r"
  proof (rule bisimulatesI)
    show "ports ?l = ports ?r" by auto
    show "?R \<subseteq> states ?l \<times> states ?r" by auto
    show "states ?l \<subseteq> fst ` ?R" by (auto simp add: image_iff)
    show "states ?r \<subseteq> snd ` ?R" by (auto simp add: image_iff)
    show "simulating ?R ?l ?r"
    proof (rule simulatingI, rule conjI; rule impI)
      fix left_triple right_triple g f
      assume in_R: "(left_triple, right_triple) \<in> ?R"
      from in_R obtain q\<^sub>1 q\<^sub>2 q\<^sub>3 where 
        l_def: "left_triple = ((q\<^sub>1,q\<^sub>2),q\<^sub>3)" and
        r_def: "right_triple = (q\<^sub>1,(q\<^sub>2,q\<^sub>3))" by blast
      {
      fix left_triple'
      assume left_trans: "left_triple g\<rightarrow>f left_triple' \<in> transitions ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) \<times>\<^sub>\<A> \<A>\<^sub>3)"
      from left_trans obtain q\<^sub>1' q\<^sub>2' q\<^sub>3' where 
        l'_def: "left_triple'= ((q\<^sub>1',q\<^sub>2'),q\<^sub>3')" by auto
      from left_trans have
        left_trans_unfolded: "((q\<^sub>1,q\<^sub>2),q\<^sub>3) g\<rightarrow>f ((q\<^sub>1',q\<^sub>2'),q\<^sub>3') \<in> transitions ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) \<times>\<^sub>\<A> \<A>\<^sub>3)"
        by (simp add: l_def l'_def)
      have q\<^sub>1_in: "q\<^sub>1 \<in> states \<A>\<^sub>1" using \<A>\<^sub>1_GA left_trans_unfolded by auto
      have q\<^sub>2_in: "q\<^sub>2 \<in> states \<A>\<^sub>2" using \<A>\<^sub>2_GA \<A>\<^sub>3_GA left_trans_unfolded by auto
      have q\<^sub>3_in: "q\<^sub>3 \<in> states \<A>\<^sub>3" using \<A>\<^sub>2_GA \<A>\<^sub>3_GA left_trans_unfolded by auto
      have targets_in_R: "(left_triple', (q\<^sub>1',(q\<^sub>2',q\<^sub>3'))) \<in> ?R"
        using \<A>\<^sub>1_GA \<A>\<^sub>2_GA \<A>\<^sub>3_GA l'_def left_trans by auto
      have right_trans: "(q\<^sub>1,(q\<^sub>2,q\<^sub>3)) g\<rightarrow>f (q\<^sub>1',(q\<^sub>2',q\<^sub>3')) \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3))"
      proof (use left_trans_unfolded in \<open>cases rule: prod_transitionE\<close>)
        case (left_async g\<^sub>1g\<^sub>2 g\<^sub>3)
        then show ?thesis
        proof (use left_async(3) in \<open>cases rule: prod_transitionE\<close>)
          case \<A>\<^sub>1_only: (left_async g\<^sub>1 g\<^sub>2)
          show ?thesis
          proof (rule prod_trans_leftI[where left_guard=g\<^sub>1 and right_guard="g\<^sub>2 \<union> g\<^sub>3"])
            show "g\<^sub>2 \<union> g\<^sub>3 \<in> ((\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3) (q\<^sub>2, q\<^sub>3)\<^sup>#)"
              by (meson \<A>\<^sub>1_only(4) \<A>\<^sub>2_GA \<A>\<^sub>3_GA \<A>\<^sub>2_\<A>\<^sub>3_disjoint left_async(4) nonenabling_components_nonenabling_product)
          qed (use q\<^sub>2_in q\<^sub>3_in \<A>\<^sub>1_only left_async in auto)
        next
          case (right_async g\<^sub>1 g\<^sub>2)
          show ?thesis
          proof (rule prod_trans_rightI[where left_guard=g\<^sub>1 and right_guard="g\<^sub>2 \<union> g\<^sub>3"])
            show "(q\<^sub>2, q\<^sub>3) (g\<^sub>2 \<union> g\<^sub>3)\<rightarrow>f (q\<^sub>2', q\<^sub>3') \<in> transitions (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3)"
              by (rule prod_trans_leftI[where left_guard=g\<^sub>2 and right_guard=g\<^sub>3], use right_async left_async q\<^sub>3_in in auto)
          qed (use q\<^sub>1_in right_async left_async in auto)
        next
          case (both_sync g\<^sub>1 g\<^sub>2 f\<^sub>1 f\<^sub>2)
          show ?thesis
          proof (rule prod_trans_bothI[where left_guard=g\<^sub>1 and right_guard="g\<^sub>2 \<union> g\<^sub>3" and left_firing=f\<^sub>1 and right_firing=f\<^sub>2])
            show "(q\<^sub>2, q\<^sub>3) (g\<^sub>2 \<union> g\<^sub>3)\<rightarrow>f\<^sub>2 (q\<^sub>2', q\<^sub>3') \<in> transitions (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3)"
              by (rule prod_trans_leftI[where left_guard=g\<^sub>2 and right_guard=g\<^sub>3], use both_sync left_async q\<^sub>3_in in auto)
          qed (use both_sync left_async in auto)
        qed
      next
        case (right_async g\<^sub>1g\<^sub>2 g\<^sub>3)
        obtain g\<^sub>1 g\<^sub>2 where
          g\<^sub>1g\<^sub>2_eq: "g\<^sub>1g\<^sub>2 = g\<^sub>1 \<union> g\<^sub>2" and
          g\<^sub>1_nonenabling: "g\<^sub>1 \<in> (\<A>\<^sub>1 q\<^sub>1\<^sup>#)" and
          g\<^sub>2_nonenabling: "g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)"
          by (meson \<A>\<^sub>1_GA \<A>\<^sub>1_\<A>\<^sub>2_disjoint \<A>\<^sub>2_GA nonenabling_product_components q\<^sub>1_in q\<^sub>2_in right_async(4))
        show ?thesis
        proof (rule prod_trans_rightI[where left_guard=g\<^sub>1 and right_guard="g\<^sub>2 \<union> g\<^sub>3"])
          show "(q\<^sub>2,q\<^sub>3) (g\<^sub>2 \<union> g\<^sub>3)\<rightarrow>f (q\<^sub>2',q\<^sub>3') \<in> transitions (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3)"
            by (rule prod_trans_rightI[where left_guard=g\<^sub>2 and right_guard=g\<^sub>3],
              use g\<^sub>1g\<^sub>2_eq right_async q\<^sub>2_in g\<^sub>2_nonenabling in auto)
        qed (use g\<^sub>1g\<^sub>2_eq right_async q\<^sub>1_in g\<^sub>1_nonenabling in auto)
      next
        case (both_sync g\<^sub>1g\<^sub>2 g\<^sub>3 f\<^sub>1f\<^sub>2 f\<^sub>3)
        then show ?thesis
        proof (use both_sync(3) in \<open>cases rule: prod_transitionE\<close>)
          case (left_async g\<^sub>1 g\<^sub>2)
          show ?thesis 
            by (rule prod_trans_bothI[where left_guard=g\<^sub>1 and right_guard="g\<^sub>3 \<union> g\<^sub>2" and left_firing=f\<^sub>1f\<^sub>2 and right_firing=f\<^sub>3],
            use both_sync left_async q\<^sub>2_in in auto)
        next
          case (right_async g\<^sub>1 g\<^sub>2)
           show ?thesis
             by (rule prod_trans_rightI[where left_guard=g\<^sub>1 and right_guard="g\<^sub>2 \<union> g\<^sub>3"],
             use both_sync right_async q\<^sub>1_in sup_assoc in auto)
        next
          case both_sync': (both_sync g\<^sub>1 g\<^sub>2 f\<^sub>1 f\<^sub>2)
          show ?thesis
            by (rule prod_trans_bothI[where left_guard="g\<^sub>1" and right_guard="g\<^sub>2 \<union> g\<^sub>3" and left_firing="f\<^sub>1" and right_firing="f\<^sub>2 \<union> f\<^sub>3"],
            use both_sync both_sync'  sup_assoc in auto)
        qed
      qed
      show "\<exists>right_triple'. right_triple g\<rightarrow>f right_triple' \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3)) \<and>
          (left_triple', right_triple') \<in> ?R"
        using r_def right_trans targets_in_R by blast
      }
      fix right_triple'
      assume right_trans: "right_triple g\<rightarrow>f right_triple' \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3))"
      from right_trans obtain q\<^sub>1' q\<^sub>2' q\<^sub>3' where 
          r'_def: "right_triple'= (q\<^sub>1',q\<^sub>2',q\<^sub>3')" by auto
      from right_trans have
        right_trans_unfolded: "(q\<^sub>1,q\<^sub>2,q\<^sub>3) g\<rightarrow>f (q\<^sub>1',q\<^sub>2',q\<^sub>3') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> (\<A>\<^sub>2 \<times>\<^sub>\<A> \<A>\<^sub>3))"
        by (simp add: r_def r'_def)
      have q\<^sub>1_in: "q\<^sub>1 \<in> states \<A>\<^sub>1" using \<A>\<^sub>1_GA right_trans_unfolded by auto
      have q\<^sub>2_in: "q\<^sub>2 \<in> states \<A>\<^sub>2" using \<A>\<^sub>2_GA \<A>\<^sub>3_GA right_trans_unfolded by auto
      have q\<^sub>3_in: "q\<^sub>3 \<in> states \<A>\<^sub>3" using \<A>\<^sub>2_GA \<A>\<^sub>3_GA right_trans_unfolded by auto
      have targets_in_R: "(((q\<^sub>1',q\<^sub>2'),q\<^sub>3'), (q\<^sub>1',(q\<^sub>2',q\<^sub>3'))) \<in> ?R"
        using \<A>\<^sub>1_GA \<A>\<^sub>2_GA \<A>\<^sub>3_GA r'_def right_trans by auto
      have left_trans: "((q\<^sub>1,q\<^sub>2),q\<^sub>3) g\<rightarrow>f ((q\<^sub>1',q\<^sub>2'), q\<^sub>3') \<in> transitions ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) \<times>\<^sub>\<A> \<A>\<^sub>3)"
      proof (use right_trans_unfolded in \<open>cases rule: prod_transitionE\<close>)
        case (left_async g\<^sub>1 g\<^sub>2g\<^sub>3)
        obtain g\<^sub>2 g\<^sub>3 where
            g\<^sub>2g\<^sub>3_eq: "g\<^sub>2g\<^sub>3 = g\<^sub>2 \<union> g\<^sub>3" and
            g\<^sub>2_nonenabling: "g\<^sub>2 \<in> (\<A>\<^sub>2 q\<^sub>2\<^sup>#)" and
            g\<^sub>3_nonenabling: "g\<^sub>3 \<in> (\<A>\<^sub>3 q\<^sub>3\<^sup>#)"
          by (meson \<A>\<^sub>2_GA \<A>\<^sub>2_\<A>\<^sub>3_disjoint \<A>\<^sub>3_GA left_async(4) nonenabling_product_components q\<^sub>2_in q\<^sub>3_in)
        show ?thesis
        proof (rule prod_trans_leftI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard="g\<^sub>3"])
          show "(q\<^sub>1, q\<^sub>2) (g\<^sub>1 \<union> g\<^sub>2)\<rightarrow>f (q\<^sub>1', q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
            by (rule prod_trans_leftI[where left_guard=g\<^sub>1 and right_guard=g\<^sub>2],
              use left_async q\<^sub>2_in g\<^sub>2_nonenabling in auto)
        qed (use g\<^sub>2g\<^sub>3_eq left_async q\<^sub>3_in g\<^sub>3_nonenabling in auto)
      next
        case (right_async g\<^sub>1 g\<^sub>2g\<^sub>3)
        show ?thesis
        proof (use right_async(3) in \<open>cases rule: prod_transitionE\<close>)
          case (left_async g\<^sub>2 g\<^sub>3)
          show ?thesis 
            by (rule prod_trans_leftI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard="g\<^sub>3"],
              use left_async right_async q\<^sub>1_in q\<^sub>3_in in auto)
      next
        case right_async': (right_async g\<^sub>2 g\<^sub>3)
        have g\<^sub>1g\<^sub>2_in: "g\<^sub>1 \<union> g\<^sub>2 \<in> ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) (q\<^sub>1, q\<^sub>2)\<^sup>#)"
          by (meson \<A>\<^sub>1_GA \<A>\<^sub>1_\<A>\<^sub>2_disjoint \<A>\<^sub>2_GA nonenabling_components_nonenabling_product right_async'(4) right_async(4))
        show ?thesis
          by (rule prod_trans_rightI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard="g\<^sub>3"],
            use q\<^sub>1_in q\<^sub>2_in g\<^sub>1g\<^sub>2_in right_async right_async' sup_assoc in auto)
      next
        case (both_sync g\<^sub>2 g\<^sub>3 f\<^sub>2 f\<^sub>3)
        show ?thesis
          by (rule prod_trans_bothI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard=g\<^sub>3 and left_firing=f\<^sub>2 and right_firing=f\<^sub>3],
          use both_sync right_async sup_assoc q\<^sub>1_in in auto)
      qed
    next
      case (both_sync g\<^sub>1 g\<^sub>2g\<^sub>3 f\<^sub>1 f\<^sub>2f\<^sub>3)
      then show ?thesis
      proof (use both_sync(4) in \<open>cases rule: prod_transitionE\<close>)
        case (left_async g\<^sub>2 g\<^sub>3)
        show ?thesis
          by (rule prod_trans_leftI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard=g\<^sub>3],
            use both_sync left_async sup_assoc q\<^sub>3_in in auto)
      next
        case (right_async g\<^sub>2 g\<^sub>3)
        show ?thesis
          by (rule prod_trans_bothI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard=g\<^sub>3 and left_firing=f\<^sub>1 and right_firing=f\<^sub>2f\<^sub>3],
            use both_sync right_async sup_assoc q\<^sub>2_in in auto)
      next
        case both_sync': (both_sync g\<^sub>2 g\<^sub>3 f\<^sub>2 f\<^sub>3)
        show ?thesis 
          by (rule prod_trans_bothI[where left_guard="g\<^sub>1 \<union> g\<^sub>2" and right_guard=g\<^sub>3 and left_firing="f\<^sub>1 \<union> f\<^sub>2" and right_firing=f\<^sub>3],
            use both_sync both_sync' sup_assoc in auto)
        qed
      qed
      show "\<exists>left_triple'. left_triple g\<rightarrow>f left_triple' \<in> transitions ((\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2) \<times>\<^sub>\<A> \<A>\<^sub>3) \<and>
          (left_triple', right_triple') \<in> ?R"
        using l_def left_trans r'_def targets_in_R by blast
    qed
  qed
  show ?thesis using R_bisim bisimilar_def by blast
qed

subsection ReoAutomata

definition reactive :: "('\<Sigma>, 'Q) guarded_automaton \<Rightarrow> bool" where
  "reactive \<A> = (\<forall>t. t \<in> transitions \<A> \<longrightarrow> firings t \<subseteq> guard t)"

lemma reactiveI [intro]: "(\<And>t. t \<in> transitions \<A> \<Longrightarrow> firings t \<subseteq> guard t) \<Longrightarrow> reactive \<A>"
  by (simp add: reactive_def)

(* removing unfired requests does not LOSE firing behaviour ? *)

definition uniform :: "('\<Sigma>, 'Q) guarded_automaton \<Rightarrow> bool" where
  "uniform \<A> = True"

lemma uniformI [intro, simp]: "uniform \<A>"
  by (simp add: uniform_def)
(*

definition uniform :: "('\<Sigma>, 'Q) guarded_automaton \<Rightarrow> bool" where
  "uniform \<A> = (\<forall>q q' g f g'. q g\<rightarrow>f q' \<in> transitions \<A> \<and> f \<subseteq> g' \<and> g' \<subseteq> g \<longrightarrow> q g'\<rightarrow>f q' \<in> transitions \<A>)"

lemma uniformI [intro]:
  "(\<And>q g f q' g'. q g\<rightarrow>f q' \<in> transitions \<A> \<Longrightarrow> f \<subseteq> g' \<Longrightarrow> g' \<subseteq> g \<Longrightarrow> q g'\<rightarrow>f q' \<in> transitions \<A>) \<Longrightarrow> uniform \<A>"
  using uniform_def by force

lemma trans_by_uniformity [intro]:
  "uniform \<A> \<Longrightarrow> q g\<rightarrow>f q' \<in> transitions \<A> \<Longrightarrow> f \<subseteq> g' \<Longrightarrow> g' \<subseteq> g \<Longrightarrow> q g'\<rightarrow>f q' \<in> transitions \<A>"
  by (auto simp add: uniform_def)
*)

definition reo_automaton :: "('\<Sigma>, 'Q) guarded_automaton \<Rightarrow> bool"  where
  "reo_automaton \<A> = (wf_guarded_automaton \<A> \<and> reactive \<A> \<and> uniform \<A>)"

lemma reo_automatonE1 [intro]: "reo_automaton \<A> \<Longrightarrow> q g\<rightarrow>f q' \<in> transitions \<A> \<Longrightarrow> f \<subseteq> g"
  using reactive_def reo_automaton_def by fastforce

lemma reo_automatonI [intro]: "wf_guarded_automaton \<A> \<Longrightarrow> reactive \<A> \<Longrightarrow> uniform \<A> \<Longrightarrow> reo_automaton \<A>"
  by (simp add: reo_automaton_def)

lemma reo_automatonD [dest]:
  assumes "reo_automaton \<A>"
  shows "wf_guarded_automaton \<A>" "reactive \<A>" "uniform \<A>"
  using assms by (auto simp add: reo_automaton_def)

lemma reo_automaton_closed_product:
  assumes 
    reo_\<A>\<^sub>1: "reo_automaton \<A>\<^sub>1" and
    reo_\<A>\<^sub>2: "reo_automaton \<A>\<^sub>2" and
    disjoint: "ports \<A>\<^sub>1 \<inter> ports \<A>\<^sub>2 = {}"
  shows "reo_automaton (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
proof (rule reo_automatonI)
  have wf_\<A>\<^sub>1: "wf_guarded_automaton \<A>\<^sub>1" by (meson reo_\<A>\<^sub>1 reo_automaton_def)
  have wf_\<A>\<^sub>2: "wf_guarded_automaton \<A>\<^sub>2" by (meson reo_\<A>\<^sub>2 reo_automaton_def)
  show "wf_guarded_automaton (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" by (meson wf_\<A>\<^sub>1 wf_\<A>\<^sub>2 wf_invariant_product)
  show "reactive (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)"
  proof (rule reactiveI)
    fix t
    assume t_in: "t \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" 
    obtain q\<^sub>1 q\<^sub>2 q\<^sub>1' q\<^sub>2' g f where t_def: "t = (q\<^sub>1,q\<^sub>2) g\<rightarrow>f (q\<^sub>1',q\<^sub>2')" by (metis surj_pair transition.cases)
    have t_unfolded: "(q\<^sub>1,q\<^sub>2) g\<rightarrow>f (q\<^sub>1',q\<^sub>2') \<in> transitions (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" using t_def t_in by blast
    show "firings t \<subseteq> guard t"
    proof (use t_unfolded in \<open>cases rule: prod_transitionE\<close>)
      case (left_async g\<^sub>1 g\<^sub>2)
      have "f \<subseteq> g\<^sub>1" by (meson left_async(3) reo_\<A>\<^sub>1 reo_automatonE1)
      then show ?thesis by (simp add: left_async(2) sup.coboundedI1 t_def)
    next
      case (right_async g\<^sub>1 g\<^sub>2)
      have "f \<subseteq> g\<^sub>2" by (meson right_async(3) reo_\<A>\<^sub>2 reo_automatonE1)
      then show ?thesis by (simp add: right_async(2) sup.coboundedI2 t_def)
    next
      case (both_sync g\<^sub>1 g\<^sub>2 f\<^sub>1 f\<^sub>2)
      then show ?thesis
        by (metis Un_mono reo_\<A>\<^sub>1 reo_\<A>\<^sub>2 reo_automatonE1 t_def transition.select_convs(2) transition.select_convs(3))
    qed
  qed
  show "uniform (\<A>\<^sub>1 \<times>\<^sub>\<A> \<A>\<^sub>2)" by simp
qed


fun synchronize where
  "synchronize a b \<A> = \<lparr> ports = ports \<A> - {a,b}, states = states \<A>,
     transitions = { q (g - {a,b})\<rightarrow>(f - {a,b}) q' |q g f q'. (q g\<rightarrow>f q' \<in> transitions \<A>) \<and> ((a \<in> f) = (b \<in> f)) \<and> (a \<in> g \<or> b \<in> g) } \<rparr>"

lemma "distinct [a,b,c,d] \<Longrightarrow> (synchronize b c ((sync a b q\<^sub>1) \<times>\<^sub>\<A> (sync c d q\<^sub>2))) = (sync a d (q\<^sub>1,q\<^sub>2))"
  apply auto
  apply (rule exI[where x="{a,b,c,d}"])
  apply (rule conjI)
   apply blast
  apply (rule exI[where x="{a,b,c,d}"])
  apply (rule conjI)
   apply blast
  apply (rule conjI)
  by blast+

lemma reo_automaton_closed_synchronization:
  assumes 
    is_reo: "reo_automaton \<A>" and
    a_port: "a \<in> ports \<A>" and
    b_port: "b \<in> ports \<A>"
  shows "reo_automaton (synchronize a b \<A>)"
proof (rule reo_automatonI)
  have \<A>_wf: "wf_guarded_automaton \<A>" by (meson is_reo reo_automaton_def)
  show "wf_guarded_automaton (synchronize a b \<A>)"
  proof (rule wf_guarded_automatonI)
    show "finite (ports (synchronize a b \<A>))" using \<A>_wf wf_guarded_automaton_def by auto
    show "finite (states (synchronize a b \<A>))" using \<A>_wf wf_guarded_automaton_def by auto
    show "source ` transitions (synchronize a b \<A>) \<subseteq> states (synchronize a b \<A>)"
      using \<A>_wf wf_implies_wf_transitions(1) by auto
    show "\<Union>(guard ` transitions (synchronize a b \<A>)) \<subseteq> ports (synchronize a b \<A>)" 
      apply auto
      using \<A>_wf by blast+
    show "\<Union> (firings ` transitions (synchronize a b \<A>)) \<subseteq> ports (synchronize a b \<A>)" 
      apply auto
      using \<A>_wf by blast+
    show "target ` transitions (synchronize a b \<A>) \<subseteq> states (synchronize a b \<A>)" 
      apply auto
      using \<A>_wf by blast+
    show "states (synchronize a b \<A>) \<noteq> {}" using \<A>_wf wf_guarded_automaton_def by auto
  qed
  show "reactive (synchronize a b \<A>)"
    apply (rule reactiveI)
    apply auto
    by (meson is_reo reo_automatonE1 subsetCE)+
  show "uniform (synchronize a b \<A>)" by blast
qed

(*
fun synchronize where
  "synchronize a b \<A> = \<lparr> ports = ports \<A> - {a,b}, states = states \<A>,
     transitions = { q (g - {a,b})\<rightarrow>(f - {a,b}) q' |q g f q'. (q g\<rightarrow>f q' \<in> transitions \<A>) \<and> ((a \<in> f) = (b \<in> f)) \<and> (a \<in> g \<or> b \<in> g) } \<rparr>"
*)

lemma wooo:
  assumes
    sync_trans: "q g\<rightarrow>f q' \<in> transitions (synchronize a b \<A>)"
  shows "q (g \<union> {a})\<rightarrow>f q' \<in> transitions \<A> \<or> q (g \<union> {b})\<rightarrow>f q' \<in> transitions \<A> \<or> q (g \<union> {a,b})\<rightarrow>f q' \<in> transitions \<A> \<or>
  q (g \<union> {a})\<rightarrow>(f \<union> {a,b}) q' \<in> transitions \<A> \<or> q (g \<union> {b})\<rightarrow>(f \<union> {a,b}) q' \<in> transitions \<A> \<or> q (g \<union> {a,b})\<rightarrow>(f \<union> {a,b}) q' \<in> transitions \<A>"
proof -
  obtain  g' f'  where 
    x: "q g'\<rightarrow>f' q' \<in> transitions \<A>" and
    "(a \<in> f') = (b \<in> f')" and
    "a \<in> g' \<or> b \<in> g'" and
    "f = f' - {a,b}" and
    "g = g' - {a,b}"
    using sync_trans by auto
  have y: "f' = f \<or> f' = f \<union> {a,b}"
    using \<open>(a \<in> f') = (b \<in> f')\<close> \<open>f = f' - {a, b}\<close> by auto
  have z: "g' = g \<union> {a} \<or> g' = g \<union> {b} \<or> g' = g \<union> {a,b}" 
    using \<open>a \<in> g' \<or> b \<in> g'\<close> \<open>g = g' - {a, b}\<close> by auto
  show ?thesis using x y z by blast
qed

lemma sync_trans_elim [elim, consumes 1]:
  assumes
    "q g\<rightarrow>f q' \<in> transitions (synchronize a b \<A>)" and
    "q (g \<union> {a})\<rightarrow>f q' \<in> transitions \<A> \<Longrightarrow> P" and
    "q (g \<union> {b})\<rightarrow>f q' \<in> transitions \<A> \<Longrightarrow> P" and
    "q (g \<union> {a,b})\<rightarrow>f q' \<in> transitions \<A> \<Longrightarrow> P" and
    "q (g \<union> {a})\<rightarrow>(f \<union> {a,b}) q' \<in> transitions \<A> \<Longrightarrow> P" and
    "q (g \<union> {b})\<rightarrow>(f \<union> {a,b}) q' \<in> transitions \<A> \<Longrightarrow> P" and
    "q (g \<union> {a,b})\<rightarrow>(f \<union> {a,b}) q' \<in> transitions \<A> \<Longrightarrow> P"
  shows P
  by (meson assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) assms(7) wooo)


(*
fun synchronize where
  "synchronize a b \<A> = \<lparr> ports = ports \<A> - {a,b}, states = states \<A>,
     transitions = { q (g - {a,b})\<rightarrow>(f - {a,b}) q' |q g f q'. (q g\<rightarrow>f q' \<in> transitions \<A>) \<and> ((a \<in> f) = (b \<in> f)) \<and> (a \<in> g \<or> b \<in> g) } \<rparr>"
*)

lemma synchronization_commutative:
  assumes
    "reo_automaton \<A>" and
    "a \<in> ports \<A>" and
    "b \<in> ports \<A>" and
    "c \<in> ports \<A>" and
    "d \<in> ports \<A>" and
    "distinct [a,b,c,d]"
  shows "synchronize a b (synchronize c d \<A>) = synchronize c d (synchronize a b \<A>)" (is "?l = ?r")
proof -
  have "states ?l = states ?r" by auto
  have "ports ?l = ports ?r" by auto
  have "transitions ?l = transitions ?r"
  proof -
    have "transitions (synchronize a b (synchronize c d \<A>)) = 
  { q (g - {a,b})\<rightarrow>(f - {a,b}) q' |q g f q'. (q g\<rightarrow>f q' \<in> transitions (synchronize c d \<A>)) \<and> ((a \<in> f) = (b \<in> f)) \<and> (a \<in> g \<or> b \<in> g) }"
      by simp
    have "transitions (synchronize c d \<A>) = 
 { q (g - {c,d})\<rightarrow>(f - {c,d}) q' |q g f q'. (q g\<rightarrow>f q' \<in> transitions \<A>) \<and> ((c \<in> f) = (d \<in> f)) \<and> (c \<in> g \<or> d \<in> g) }"
      by simp
    have "transitions (synchronize a b (synchronize c d \<A>)) = 
 { q (g - {a,b,c,d})\<rightarrow>(f - {a,b,c,d}) q' |q g f q'. (q g\<rightarrow>f q' \<in> transitions \<A>) \<and> ((a \<in> f) = (b \<in> f)) \<and> ((c \<in> f) = (d \<in> f)) \<and> (a \<in> g \<or> b \<in> g) \<and> (c \<in> g \<or> d \<in> g) }"
      
  proof (rule set_eqI, rule iffI)
    fix t
    assume t_in: "t \<in> transitions (synchronize a b (synchronize c d \<A>))"
    obtain q g f q' where t_def: "t = q g\<rightarrow>f q'" using transition.cases by blast
    have t_in': "q g\<rightarrow>f q' \<in> transitions (synchronize a b (synchronize c d \<A>))" using t_in t_def by auto
    have "a \<notin> f" using mem_Collect_eq t_def t_in by auto
    have "b \<notin> f" using mem_Collect_eq t_def t_in by auto
    have "a \<notin> g" using mem_Collect_eq t_def t_in by auto
    have "b \<notin> g" using mem_Collect_eq t_def t_in by auto
    have "q g\<rightarrow>f q' \<in> transitions (synchronize c d (synchronize a b \<A>))"
      apply (rule sync_trans_elim[OF t_in'])
    proof -
      assume ff: "q (g \<union> {a})\<rightarrow>f q' \<in> transitions (synchronize c d \<A>)"
      have "c \<notin> f"
        using ff by auto
      have "d \<notin> f"
        using ff by auto
      show "q g\<rightarrow>f q' \<in> transitions (synchronize c d (synchronize a b \<A>))"
        apply (rule sync_trans_elim[OF ff])
             apply auto[1]
             apply (rule exI[where x="{a,b,c,d}"])
        apply (rule conjI)
   



(*
section GuardedStrings

datatype '\<Sigma> guard = 
    Var '\<Sigma> 
  | Top ("\<top>\<^sub>g")
  | Bottom ("\<bottom>\<^sub>g")
  | Or "'\<Sigma> guard" "'\<Sigma> guard" ("_ \<or>\<^sub>g _")
  | And "'\<Sigma> guard" "'\<Sigma> guard" ("_ \<and>\<^sub>g _")
  | Not "'\<Sigma> guard" ("\<not>\<^sub>g")

primrec vars :: "'\<Sigma> guard \<Rightarrow> '\<Sigma> set" where
  "vars (Var \<sigma>) = { \<sigma> }"
| "vars \<top>\<^sub>g = {}"
| "vars \<bottom>\<^sub>g = {}"
| "vars (g\<^sub>1 \<or>\<^sub>g g\<^sub>2) = vars g\<^sub>1 \<union> vars g\<^sub>2"
| "vars (g\<^sub>1 \<and>\<^sub>g g\<^sub>2) = vars g\<^sub>1 \<union> vars g\<^sub>2"
| "vars (\<not>\<^sub>g g) = vars g"

type_synonym 'v valuation = "'v \<Rightarrow> bool"

primrec interpret_guard :: "'\<Sigma> valuation \<Rightarrow> '\<Sigma> guard \<Rightarrow> bool" ("\<I>") where
  "\<I> v (Var \<sigma>) = v \<sigma>"
| "\<I> _ \<top>\<^sub>g = True" 
| "\<I> _ \<bottom>\<^sub>g = False" 
| "\<I> v (g\<^sub>1 \<or>\<^sub>g g\<^sub>2) = (\<I> v g\<^sub>1 \<or> \<I> v g\<^sub>2)"
| "\<I> v (g\<^sub>1 \<and>\<^sub>g g\<^sub>2) = (\<I> v g\<^sub>1 \<and> \<I> v g\<^sub>2)"
| "\<I> v (\<not>\<^sub>g g) = (\<not> \<I> v g)"

definition leq :: "'\<Sigma> guard \<Rightarrow> '\<Sigma> guard \<Rightarrow> bool" where
  "leq g\<^sub>1 g\<^sub>2 = (\<forall>v. (\<I> v (g\<^sub>1 \<and>\<^sub>g g\<^sub>2) = \<I> v g\<^sub>1))"

definition eq :: "'\<Sigma> guard \<Rightarrow> '\<Sigma> guard \<Rightarrow> bool" ("_ \<approx> _" [100,100]) where
  "eq g\<^sub>1 g\<^sub>2 = (\<forall>v. \<I> v g\<^sub>1 = \<I> v g\<^sub>2)"

fun is_literal :: "'\<Sigma> guard \<Rightarrow> bool" where
  "is_literal (Var _) = True"
| "is_literal (\<not>\<^sub>g (Var _)) = True"
| "is_literal _ = False"

locale signature =
  fixes ports :: "'\<Sigma> list"
  assumes "finite (set ports)"
begin

definition At\<^sub>\<Sigma> :: "'\<Sigma> guard set" where
  "At\<^sub>\<Sigma> = { g . is_atom g}"

  



fun dnf :: "'\<Sigma> guard \<Rightarrow> bool" where
  "dnf (g\<^sub>1 \<or>\<^sub>g g\<^sub>2) = (dnf g\<^sub>1 \<and> dnf g\<^sub>2)"
| "dnf g = is_atom g"

definition norm :: "'\<Sigma> guard \<Rightarrow> '\<Sigma> guard set" where
  "norm g = { g' . dnf g' \<and> g \<approx> g' }"

(* more todo *)

section GuardedAutomata

record ('\<Sigma>, 'Q) transition =
  source :: 'Q
  guard :: "'\<Sigma> guard"
  firings :: "'\<Sigma> set"
  target :: 'Q

record ('\<Sigma>, 'Q) guarded_automaton =
  ports :: "'\<Sigma> set"
  states :: "'Q set"
  transitions :: "('\<Sigma>, 'Q) transition set"

locale guarded_automaton =
  fixes \<A> :: "('\<Sigma>, 'Q) guarded_automaton"
  assumes 
    "finite (ports \<A>)" and
    "finite (states \<A>)" and
    "source ` transitions \<A> \<subseteq> states \<A>"
    "\<Union> ((vars \<circ> guard) ` transitions \<A>) \<subseteq> ports \<A>"
    "target ` transitions \<A> \<subseteq> states \<A>"

definition bisimulates where
  "bisimulates R \<A>\<^sub>1 \<A>\<^sub>2 = (R \<subseteq> states \<A>\<^sub>1 \<times> states \<A>\<^sub>2 \<and> (\<forall> t \<in> transitions \<A>\<^sub>1 . t = t))" (* todo *)

*)