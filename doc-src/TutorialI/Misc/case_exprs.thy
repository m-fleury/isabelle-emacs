(*<*)
theory case_exprs = Main:
(*>*)

subsection{*Case expressions*}

text{*\label{sec:case-expressions}
HOL also features \isaindexbold{case}-expressions for analyzing
elements of a datatype. For example,
@{term[display]"case xs of [] => 1 | y#ys => y"}
evaluates to @{term"1"} if @{term"xs"} is @{term"[]"} and to @{term"y"} if 
@{term"xs"} is @{term"y#ys"}. (Since the result in both branches must be of
the same type, it follows that @{term"y"} is of type @{typ"nat"} and hence
that @{term"xs"} is of type @{typ"nat list"}.)

In general, if $e$ is a term of the datatype $t$ defined in
\S\ref{sec:general-datatype} above, the corresponding
@{text"case"}-expression analyzing $e$ is
\[
\begin{array}{rrcl}
@{text"case"}~e~@{text"of"} & C@1~x@ {11}~\dots~x@ {1k@1} & \To & e@1 \\
                           \vdots \\
                           \mid & C@m~x@ {m1}~\dots~x@ {mk@m} & \To & e@m
\end{array}
\]

\begin{warn}
\emph{All} constructors must be present, their order is fixed, and nested
patterns are not supported.  Violating these restrictions results in strange
error messages.
\end{warn}
\noindent
Nested patterns can be simulated by nested @{text"case"}-expressions: instead
of
@{text[display]"case xs of [] => 1 | [x] => x | x # (y # zs) => y"}
write
@{term[display,eta_contract=false,margin=50]"case xs of [] => 1 | x#ys => (case ys of [] => x | y#zs => y)"}

Note that @{text"case"}-expressions may need to be enclosed in parentheses to
indicate their scope
*}

subsection{*Structural induction and case distinction*}

text{*
\indexbold{structural induction}
\indexbold{induction!structural}
\indexbold{case distinction}
Almost all the basic laws about a datatype are applied automatically during
simplification. Only induction is invoked by hand via \isaindex{induct_tac},
which works for any datatype. In some cases, induction is overkill and a case
distinction over all constructors of the datatype suffices. This is performed
by \isaindexbold{case_tac}. A trivial example:
*}

lemma "(case xs of [] \<Rightarrow> [] | y#ys \<Rightarrow> xs) = xs";
apply(case_tac xs);

txt{*\noindent
results in the proof state
\begin{isabelle}
~1.~xs~=~[]~{\isasymLongrightarrow}~(case~xs~of~[]~{\isasymRightarrow}~[]~|~y~\#~ys~{\isasymRightarrow}~xs)~=~xs\isanewline
~2.~{\isasymAnd}a~list.~xs=a\#list~{\isasymLongrightarrow}~(case~xs~of~[]~{\isasymRightarrow}~[]~|~y\#ys~{\isasymRightarrow}~xs)~=~xs%
\end{isabelle}
which is solved automatically:
*}

apply(auto)
(*<*)done(*>*)
text{*
Note that we do not need to give a lemma a name if we do not intend to refer
to it explicitly in the future.
*}

(*<*)
end
(*>*)
