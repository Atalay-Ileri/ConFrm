### Base Definitions

$State : Type$ 

​	Type of states.

$User : Type$ 

​	Type of users 

$Prog: Type \rightarrow Type$ 

​	Type of programs, parameterized by return value



### System defined classically

Our system is $\{ S, U, P, Exec\}​$ where

* $S = \{s \ | \ s:State\}​$ 	Set of states,

* $U = \{u \ | \ u:User\}$ 		Set of users,

* $P = \{p\ |\ \exists T, p : Prog\ T \}​$	Set of programs

* $Exec : \forall T, State \rightarrow User \rightarrow Prog\ T \rightarrow  T \rightarrow  State \rightarrow Prop​$

  ​	Operational semantics



### System as an LTS

LTS is $\{Q, \Sigma, \rightarrow\}​$ where 

* $Q​$ is set of states, 

* $\Sigma​$ is set of operations, and 

* $\rightarrow_{\Sigma}​$ is the transition relation from $Q \times \Sigma​$ to $Q​$.

  

$Q = \{ s\ |\ s \in S \wedge P(s) \}​$ where $P​$ is the well-formedness predicate.

​	Informally, it is set of states that satisfies a certain predicate. 



$\Sigma = \{ (u, p, r)\ |\  \exists T, u \in U \wedge p \in P \wedge p : Prog\ T \wedge r : T\}​$

​	Informally, it is triplet of user, program and return value pairs.



$\rightarrow_{\Sigma} = \{ (s, s')\ |\ s, s' \in Q \wedge \exists (u, p, r) \in \Sigma, Exec\ s\ u\ p\ r\ s' \}​$

​	Informally, pair of states,  such that there exists a program $p​$ that

​	executes from first one to second one and returns $r$



### Other definitions

$EQ : User \rightarrow State \rightarrow State \rightarrow Prop$

​	An equivalence relation between states with respect to a user.



--------



### Data NonInterference	

​	Same as showing EQ~u~ is a (bi)simulation for our transition system.

---

### Definitions from Sangiorgi D. "On the Origins of Bisimulation and Coinduction"

#### Finitely Branching

An LTS is finitely branching if $\forall s, \{ s' : \exists \mu, s \xrightarrow{\mu} s' \}$ is finite.



#### Image Finite

An LTS is image finite if $\forall s\ \mu,  \{ s' : s \xrightarrow{\mu} s' \}$ is finite.



#### Stratification of Bisimilarity

Let $W​$ be the states of an LTS. We set:

- $\sim_0\ := W \times W$
- $s \sim_{n+1} t​$, for $n \ge 0​$, if:
  (1) $\forall s', s \xrightarrow{\mu} s' \rightarrow \exists t', t \xrightarrow{\mu} t' \wedge s' \sim_n t'​$
  (2)  $\forall t', t \xrightarrow{\mu} t' \rightarrow \exists s', s \xrightarrow{\mu} s' \wedge s' \sim_n t'​$
- $\sim_{\omega}\ := \bigcap_{n \ge 0} \sim_n$



In general, $\sim_{\omega}$ does not coincide with $\sim​$. 

However if LTS is finitely branching (or image finite), $\sim_{\omega}$ and $\sim$ coincides.

