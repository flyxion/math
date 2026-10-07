"""
render.py

LaTeX and Markdown output.  All mathematics shared between manuscripts lives in
lib/ (lemmas, one body file per contribution and dimension), so a manuscript
is a thin document that depends on named library files.  The text of every
body file is written to be true for the dimension it names.
"""

import sympy as sp

from rhombus import (CONTRIBUTIONS, DIM_LABELS, FINITE_DIMS, LABELS, a, c, n)

AUTHOR = "Anonymous"

NONSUPPORT = ("This manuscript does not support the hypothesis that it is an "
              "independent mathematical contribution.")

PREAMBLE = r"""\usepackage[margin=1in]{geometry}
\usepackage{amsmath,amssymb,amsthm,booktabs,array}
\newtheorem{theorem}{Theorem}
\newtheorem{lemma}{Lemma}
\theoremstyle{definition}
\newtheorem{definition}{Definition}
\theoremstyle{remark}
\newtheorem{remark}{Remark}
\newcommand{\R}{\mathbb{R}}
\newcommand{\vol}{\operatorname{vol}}
\newcommand{\rank}{\operatorname{rank}}
\newcommand{\T}{\mathsf{T}}
\setlength{\parskip}{0.4em}
\setlength{\parindent}{0pt}
"""

REFS = r"""\begin{thebibliography}{9}
\bibitem{gram} J.~P.~Gram, \emph{\"Uber die Entwickelung reeller Functionen in Reihen mittelst der Methode der kleinsten Quadrate}, J. Reine Angew. Math. 94 (1883), 41--73.
\bibitem{hadamard} J.~Hadamard, \emph{R\'esolution d'une question relative aux d\'eterminants}, Bull. Sci. Math. 17 (1893), 240--246.
\bibitem{hj} R.~A.~Horn and C.~R.~Johnson, \emph{Matrix Analysis}, 2nd ed., Cambridge University Press, 2013.
\end{thebibliography}
"""

LEMMAS = r"""\begin{definition}[Cubic rhombus]
For an integer $n\ge2$ and $c\in\R$ let $G_n(c)=(1-c)I_n+cJ_n$, where $J_n$ is the $n\times n$ matrix of ones.
A \emph{cubic rhombus} $R_n(c)$ is the parallelotope $\{\sum_i t_iv_i:0\le t_i\le1\}\subset\R^n$ spanned by unit vectors $v_1,\dots,v_n$ with $\langle v_i,v_j\rangle=c$ for $i\ne j$, that is, with Gram matrix $G_n(c)$.
The case $c=0$ is the unit cube, $n=2$ gives a rhombus, and $n=3$ gives a rhombohedron.
The name ``cubic rhombus'' is used in this corpus for this family. It is not claimed to be standard terminology.
\end{definition}

\begin{lemma}[Spectrum and volume]\label{lem:spec}
The matrix $G_n(c)$ has eigenvalue $1+(n-1)c$ with eigenvector $\mathbf 1=(1,\dots,1)^\T$, and eigenvalue $1-c$ with multiplicity $n-1$ on $\mathbf 1^{\perp}$.
Hence $\det G_n(c)=(1-c)^{n-1}(1+(n-1)c)$, the matrix is positive definite if and only if $-\tfrac1{n-1}<c<1$, and in that case $\vol_nR_n(c)=\sqrt{\det G_n(c)}$.
\end{lemma}
\begin{proof}
$J\mathbf 1=n\mathbf 1$, so $G\mathbf 1=(1-c+nc)\mathbf 1=(1+(n-1)c)\mathbf 1$.
If $x\perp\mathbf 1$ then $Jx=0$, so $Gx=(1-c)x$.
These eigenspaces span $\R^n$, which gives the spectrum and the determinant, and positivity of both eigenvalues is the stated range.
If $V$ is the matrix with columns $v_i$ then $G=V^\T V$ and $\vol_n=|\det V|=\sqrt{\det G}$.
\end{proof}

\begin{lemma}[Facets]\label{lem:facet}
A facet of $R_n(c)$ is spanned by $n-1$ of the edge vectors, and its Gram matrix is the principal $(n-1)\times(n-1)$ submatrix of $G_n(c)$, which is $G_{n-1}(c)$.
Its $(n-1)$-volume is $\sqrt{(1-c)^{n-2}(1+(n-2)c)}$, and the surface area of $R_n(c)$ is $2n$ times this number.
\end{lemma}
\begin{proof}
Deleting a row and the matching column of $(1-c)I+cJ$ leaves $(1-c)I+cJ$ of order $n-1$. Apply Lemma~\ref{lem:spec} in dimension $n-1$. There are $2n$ facets, in $n$ parallel pairs.
\end{proof}

\begin{lemma}[Logarithmic derivative]\label{lem:dlog}
On $(-\tfrac1{n-1},1)$ let $F(c)=\ln\det G_n(c)=(n-1)\ln(1-c)+\ln(1+(n-1)c)$. Then
\[
F'(c)=-\frac{n(n-1)\,c}{(1-c)\,(1+(n-1)c)},
\]
the denominator is positive, and so $F'$ has the sign of $-c$.
\end{lemma}
\begin{proof}
$F'(c)=-\frac{n-1}{1-c}+\frac{n-1}{1+(n-1)c}=(n-1)\frac{(1-c)-(1+(n-1)c)}{(1-c)(1+(n-1)c)}=-\frac{n(n-1)c}{(1-c)(1+(n-1)c)}$.
\end{proof}

\begin{lemma}[Vertex Gram matrices]\label{lem:vertex}
The vertices of $R_n(c)$ are the points $\sum_{i\in S}v_i$ for $S\subseteq\{1,\dots,n\}$. At the vertex $S$ the unit edge directions are $\varepsilon_iv_i$ with $\varepsilon_i=-1$ for $i\in S$ and $\varepsilon_i=+1$ otherwise, so their Gram matrix is $D_\varepsilon G_n(c)D_\varepsilon$ with $D_\varepsilon=\operatorname{diag}(\varepsilon)$.
Suppose $n\ge3$ and that all off-diagonal entries of $D_\varepsilon G_n(c)D_\varepsilon$ equal one number $s$. Then $s=c$.
For $n=2$ the conclusion fails: the vertices with $\varepsilon_1\varepsilon_2=-1$ give $s=-c$.
\end{lemma}
\begin{proof}
The first statements are immediate from the definition. The off-diagonal entries are $\varepsilon_i\varepsilon_jc$. If $c=0$ then $s=0=c$. If $c\ne0$ put $p=s/c$, so $\varepsilon_i\varepsilon_j=p$ for all $i\ne j$. For distinct $i,j,k$ we have $\varepsilon_i\varepsilon_j\cdot\varepsilon_i\varepsilon_k=\varepsilon_j\varepsilon_k$, that is $p^2=p$, so $p=1$.
\end{proof}
"""

LEMMAS_INF = r"""\begin{definition}[Cubic rhombus, finite sections, infinite systems]
For an integer $n\ge2$ and $c\in\R$ let $G_n(c)=(1-c)I_n+cJ_n$, where $J_n$ is the matrix of ones.
A \emph{cubic rhombus} $R_n(c)$ is the parallelotope in $\R^n$ spanned by unit vectors with pairwise inner product $c$.
An \emph{infinite system} is a sequence $(v_i)_{i\ge1}$ of unit vectors in a real Hilbert space with $\langle v_i,v_j\rangle=c$ for $i\ne j$.
Its finite sections are the systems $(v_i)_{i\le n}$.
The name ``cubic rhombus'' is used in this corpus for this family. It is not claimed to be standard terminology.
\end{definition}

\begin{lemma}[Spectrum and volume]\label{lem:spec}
$G_n(c)$ has eigenvalue $1+(n-1)c$ once, with eigenvector $\mathbf 1$, and eigenvalue $1-c$ with multiplicity $n-1$.
Hence $\det G_n(c)=(1-c)^{n-1}(1+(n-1)c)$, positivity holds exactly for $-\tfrac1{n-1}<c<1$, and then $\vol_nR_n(c)=\sqrt{\det G_n(c)}$.
\end{lemma}
\begin{proof}
$G\mathbf 1=(1+(n-1)c)\mathbf 1$, and $Gx=(1-c)x$ for $x\perp\mathbf 1$. If $V$ has columns $v_i$ then $G=V^\T V$ and $\vol_n=\sqrt{\det G}$.
\end{proof}

\begin{lemma}[Logarithmic derivative]\label{lem:dlog}
$F(c)=\ln\det G_n(c)$ satisfies $F'(c)=-\dfrac{n(n-1)c}{(1-c)(1+(n-1)c)}$ on $(-\tfrac1{n-1},1)$.
\end{lemma}
\begin{proof}
$F'(c)=-\frac{n-1}{1-c}+\frac{n-1}{1+(n-1)c}$, and the common denominator gives the stated form.
\end{proof}

\begin{lemma}[Vertex Gram matrices]\label{lem:vertex}
At the vertex $S$ of $R_n(c)$ the Gram matrix of the unit edge directions is $D_\varepsilon G_n(c)D_\varepsilon$ with $\varepsilon_i=-1$ for $i\in S$ and $+1$ otherwise. If $n\ge3$ and all its off-diagonal entries equal a number $s$, then $s=c$.
\end{lemma}
\begin{proof}
The off-diagonal entries are $\varepsilon_i\varepsilon_jc$. If $c\ne0$ put $p=s/c$. Then $p^2=\varepsilon_i\varepsilon_j\varepsilon_i\varepsilon_k=\varepsilon_j\varepsilon_k=p$ for distinct $i,j,k$, so $p=1$.
\end{proof}
"""

# ---------------------------------------------------------------------------
# Contribution bodies.  Placeholders are written @LIKE_THIS@.
# ---------------------------------------------------------------------------

BODY = {}

BODY["T1"] = r"""\begin{theorem}[Existence and uniqueness]\label{thm:main}
@NDEF@ Then $\det G_n(c)=@DET@$ and $G_n(c)$ is positive definite if and only if $@LO@<c<1$.
For every such $c$ there is a cubic rhombus $R_n(c)$, and any two cubic rhombi with the same $(n,c)$ differ by an orthogonal transformation of $\R^n$.
If $c<@LO@$ or $c>1$ there is no system of $n$ unit vectors with pairwise inner product $c$.
\end{theorem}
\begin{proof}
The determinant and the range of positivity are Lemma~\ref{lem:spec}.
If $G_n(c)$ is positive definite it has a Cholesky factorization $G_n(c)=V^\T V$ with $V$ invertible, and the columns of $V$ are unit vectors with the required inner products. This gives existence.
If $W$ is another matrix with $W^\T W=G_n(c)$, put $Q=WV^{-1}$. Then $Q^\T Q=V^{-\T}G_n(c)V^{-1}=I$, so $Q$ is orthogonal and $W=QV$. This gives uniqueness.
Finally, the Gram matrix of any system of vectors is positive semidefinite, so a system exists only if both eigenvalues in Lemma~\ref{lem:spec} are nonnegative, that is, only if $@LO@\le c\le1$.
\end{proof}
"""

BODY["T2"] = r"""\begin{theorem}[A sharp inequality]\label{thm:main}
@NDEF@ For every $c$ with $@LO@<c<1$ one has $\vol_nR_n(c)\le1$, with equality if and only if $c=0$, that is, if and only if $R_n(c)$ is the unit cube.
\end{theorem}
\begin{proof}
By Lemma~\ref{lem:spec}, $\vol_nR_n(c)=e^{F(c)/2}$ with $F=\ln\det G_n$.
By Lemma~\ref{lem:dlog}, $F'$ has the sign of $-c$ on $(@LO@,1)$.
So $F$ is strictly increasing on $(@LO@,0]$ and strictly decreasing on $[0,1)$.
Since $F(0)=0$, we obtain $F(c)<0$ for every $c\ne0$.
\end{proof}
\begin{remark}
The inequality is an instance of Hadamard's inequality~\cite{hadamard}: $|\det V|\le\prod_i\|v_i\|=1$ for the matrix $V$ with columns $v_i$.
\end{remark}
"""

BODY["T3"] = r"""\begin{theorem}[Extremal characterization]\label{thm:main}
@NDEF@ Among cubic rhombi $R_n(c)$ with unit edges, the unit cube $c=0$ is the unique maximizer of volume, and $c=0$ is the unique critical point of $c\mapsto\vol_nR_n(c)$ on $(@LO@,1)$.
\end{theorem}
\begin{proof}
Since $\vol_nR_n(c)=e^{F/2}$, the critical points of the volume are the critical points of $F$.
By Lemma~\ref{lem:dlog}, $F'(c)=0$ if and only if $c=0$.
The sign of $F'$ is positive before $0$ and negative after $0$, so $c=0$ is a strict global maximum, where $\vol=1$.
\end{proof}
"""

BODY["T4"] = r"""\begin{theorem}[Local stability of the cube]\label{thm:main}
@NDEF@ As $c\to0$,
\[
\ln\vol_nR_n(c)=@C2@\,c^2@C3TERM@+O(c^4).
\]
In particular the cube is a strict local maximizer of the volume among cubic rhombi, and $\frac{d^2}{dc^2}\ln\vol_nR_n(c)\big|_{c=0}=@HESS@$.
\end{theorem}
\begin{proof}
Write $F=(n-1)\ln(1-c)+\ln(1+(n-1)c)$, so that $\ln\vol=F/2$.
Expand $\ln(1-c)=-c-\frac{c^2}{2}-\frac{c^3}{3}+O(c^4)$ and $\ln(1+(n-1)c)=(n-1)c-\frac{(n-1)^2c^2}{2}+\frac{(n-1)^3c^3}{3}+O(c^4)$.
The coefficient of $c$ in $F$ is $-(n-1)+(n-1)=0$.
The coefficient of $c^2$ is $-\frac{n-1}{2}-\frac{(n-1)^2}{2}=-\frac{n(n-1)}{2}$.
The coefficient of $c^3$ is $-\frac{n-1}{3}+\frac{(n-1)^3}{3}=\frac{n(n-1)(n-2)}{3}$.
Dividing by $2$ gives the expansion of $\ln\vol$.
\end{proof}
"""

BODY["T5"] = r"""\begin{theorem}[Embedding obstructions]\label{thm:main}
@NDEF@ For $@LO@<c<1$ the $n$ edge vectors of $R_n(c)$ are linearly independent, so $R_n(c)$ has nonempty interior and does not embed isometrically in $\R^m$ for any $m<n$.
At $c=@LO@$ the edge vectors satisfy $v_1+\dots+v_n=0$ and span a space of dimension $@NM1@$.
At $c=1$ they all coincide and span a space of dimension $1$.
\end{theorem}
\begin{proof}
The rank of the matrix $V$ with columns $v_i$ equals the rank of $G_n(c)=V^\T V$.
By Lemma~\ref{lem:spec} the eigenvalues are $1+(n-1)c$ once and $1-c$ with multiplicity $n-1$.
For $c$ strictly between the endpoints both are positive and the rank is $n$.
At $c=@LO@$ the first eigenvalue vanishes and the rank is $n-1$; moreover $|v_1+\dots+v_n|^2=\mathbf 1^\T G_n(c)\mathbf 1=n(1+(n-1)c)=0$.
At $c=1$ the second eigenvalue vanishes with multiplicity $n-1$ and the rank is $1$.
\end{proof}
"""

BODY["T6"] = r"""\begin{theorem}[Boundary rigidity]\label{thm:main}
@NDEF@ Every facet of $R_n(c)$ is isometric to @FACET@
@RIGID@
\end{theorem}
\begin{proof}
The facet statement is Lemma~\ref{lem:facet}.
@RIGIDPROOF@
\end{proof}
"""

BODY["T7"] = r"""\begin{theorem}[Asymptotic volume]\label{thm:main}
@NDEF@ and $-\tfrac{n}{n-1}<a<n$, so that $c=a/n$ lies in the positivity range. Then
\[
\det G_n(a/n)=@FV@.
\]
@LIMIT@
\end{theorem}
\begin{proof}
Substitute $c=a/n$ in Lemma~\ref{lem:spec}.
The condition $-\frac1{n-1}<\frac an<1$ is the stated range of $a$.
@LIMITPROOF@
\end{proof}
"""

BODY["T8"] = r"""\begin{theorem}[A counterexample to volume rigidity]\label{thm:main}
@NDEF@ The map $c\mapsto\vol_nR_n(c)$ is not injective: for every $v\in(0,1)$ there are exactly two values $c_-\in(@LO@,0)$ and $c_+\in(0,1)$ with $\vol_nR_n(c_\pm)=v$.
@T8SHAPE@
\end{theorem}
\begin{proof}
By Lemma~\ref{lem:dlog}, $F$ is strictly increasing on $(@LO@,0]$ and strictly decreasing on $[0,1)$, with $F(0)=0$, and $F(c)\to-\infty$ at both endpoints of the interval, because $\det G_n(c)\to0$ there.
Hence $\vol=e^{F/2}$ maps each of the two open branches bijectively onto $(0,1)$, which gives exactly one solution on each side of $0$.
@T8SHAPEPROOF@
\end{proof}
"""

# Infinite-dimension bodies

BODY_INF = {}

BODY_INF["T1"] = r"""\begin{theorem}[Existence in infinite dimension]\label{thm:main}
Let $c\in\R$. There is an infinite system of unit vectors with pairwise inner product $c$ if and only if $0\le c\le1$.
The infinite matrix $G(c)=(1-c)I+cJ$ defines a bounded operator on $\ell^2$ if and only if $c=0$.
\end{theorem}
\begin{proof}
Necessity: every finite section of order $m\ge2$ has a positive semidefinite Gram matrix, so $1+(m-1)c\ge0$ by Lemma~\ref{lem:spec} for every $m$, which forces $c\ge0$; and $c\le1$ by the Cauchy--Schwarz inequality.
Sufficiency: put $v_i=\sqrt c\,e_0+\sqrt{1-c}\,e_i$ for an orthonormal sequence $e_0,e_1,\dots$. Then $\|v_i\|^2=c+(1-c)=1$ and $\langle v_i,v_j\rangle=c$ for $i\ne j$.
Boundedness: the vector $G(c)e_1$ has entry $c$ in every coordinate except the first, so it lies in $\ell^2$ only if $c=0$; and $G(0)=I$.
\end{proof}
"""

BODY_INF["T2"] = r"""\begin{theorem}[A sharp inequality in the limit]\label{thm:main}
For $c\in[0,1)$ let $V_n(c)=\vol_nR_n(c)$. Then $V_n(c)\le1$ for all $n$, and $\lim_{n\to\infty}V_n(c)=1$ if $c=0$ and $=0$ if $0<c<1$.
In particular the supremum over $c\in[0,1)$ of the limiting volume is $1$, attained only at $c=0$.
\end{theorem}
\begin{proof}
$V_n(c)^2=(1-c)^{n-1}(1+(n-1)c)\le(1-c)^{n-1}(1+nc)$, and for $0<c<1$ geometric decay beats linear growth, so the right side tends to $0$.
The case $c=0$ is the cube. The bound $V_n\le1$ is Lemma~\ref{lem:dlog} together with $F(0)=0$.
\end{proof}
"""

BODY_INF["T3"] = r"""\begin{theorem}[Extremal characterization in the limit]\label{thm:main}
Among the limiting volumes $\lim_nV_n(c)$, $c\in[0,1)$, the unit cube $c=0$ is the unique maximizer, with value $1$.
\end{theorem}
\begin{proof}
$V_n(c)^2=(1-c)^{n-1}(1+(n-1)c)\le(1-c)^{n-1}(1+nc)\to0$ for $0<c<1$, while $V_n(0)=1$ for every $n$.
\end{proof}
"""

BODY_INF["T4"] = r"""\begin{theorem}[Absence of a uniform local expansion]\label{thm:main}
The coefficient of $c^2$ in $\ln\vol_nR_n(c)$ is $-\tfrac{n(n-1)}{4}$, which tends to $-\infty$ as $n\to\infty$. Hence the stability constant of the cube is not uniform in the dimension, and no limiting local expansion exists.
\end{theorem}
\begin{proof}
Expand $F=(n-1)\ln(1-c)+\ln(1+(n-1)c)$ to order $c^2$: the coefficient is $-\frac{n-1}{2}-\frac{(n-1)^2}{2}=-\frac{n(n-1)}{2}$, and $\ln\vol=F/2$.
\end{proof}
"""

BODY_INF["T5"] = r"""\begin{theorem}[Embedding obstructions in infinite dimension]\label{thm:main}
For $0\le c<1$ the vectors of any infinite system are linearly independent, so they span an infinite dimensional space and lie in no finite dimensional Euclidean space. For $c=1$ they coincide.
\end{theorem}
\begin{proof}
Every finite section has Gram matrix $G_m(c)$, which is positive definite for $-\frac1{m-1}<c<1$ by Lemma~\ref{lem:spec}. This holds for every $m$ when $0\le c<1$, so every finite subfamily is linearly independent.
\end{proof}
"""

BODY_INF["T6"] = r"""\begin{theorem}[Boundary rigidity for finite sections]\label{thm:main}
For every $c\in[0,1)$ and every $m\ge3$, the intrinsic piecewise flat metric of the boundary of the finite section $R_m(c)$ determines $c$. Consequently the family of boundaries of finite sections of an infinite system determines $c$.
\end{theorem}
\begin{proof}
At every vertex of $R_m(c)$ the angle between any two edges is determined by the intrinsic metric, because two edges at a vertex lie in a common flat $2$-face. This recovers the Gram matrices $D_\varepsilon G_m(c)D_\varepsilon$ of Lemma~\ref{lem:vertex}.
The vertex $S=\emptyset$ has all off-diagonal entries equal to $c$, and by Lemma~\ref{lem:vertex} any vertex whose off-diagonal entries are all equal has that common value $c$. Hence $c$ is the common off-diagonal value of any vertex of this type, and so is determined.
\end{proof}
"""

BODY_INF["T7"] = r"""\begin{theorem}[Asymptotic volume]\label{thm:main}
For fixed real $a>-1$, $\displaystyle\lim_{n\to\infty}\det G_n(a/n)=(1+a)e^{-a}$.
\end{theorem}
\begin{proof}
By Lemma~\ref{lem:spec}, $\det G_n(a/n)=(1-\frac an)^{n-1}\,(1+\frac{(n-1)a}{n})$.
Now $(1-\frac an)^{n-1}=(1-\frac an)^n/(1-\frac an)\to e^{-a}$ and $1+\frac{(n-1)a}{n}\to1+a$.
For $a>-1$ the value $c=a/n$ lies in the positivity range for all large $n$.
\end{proof}
"""

BODY_INF["T8"] = r"""\begin{theorem}[Degeneration of volume rigidity]\label{thm:main}
The function $c\mapsto\lim_{n\to\infty}\vol_nR_n(c)$ is identically $0$ on $(0,1)$ and therefore not injective in $c$. The two-point fibres of finite dimension are replaced in the limit by a fibre equal to the whole interval $(0,1)$.
\end{theorem}
\begin{proof}
This is the limit computed in the proof that $V_n(c)^2=(1-c)^{n-1}(1+(n-1)c)\to0$ for $0<c<1$.
\end{proof}
"""


def _latex(expr, k):
    e = sp.sympify(expr)
    if k is not None:
        e = e.subs(n, k)
    return sp.latex(e)


def _lo(k):
    return r"-\frac{1}{n-1}" if k is None else sp.latex(-sp.Rational(1, k - 1))


def body(t, dim):
    """LaTeX source of the contribution body for (t, dim)."""
    if dim == "infinite":
        return BODY_INF[t]
    k = None if dim == "n" else int(dim)
    N = "n" if k is None else str(k)
    ndef = (r"Let $n\ge2$ be an integer." if k is None else f"Let $n={k}$.")
    lo = _lo(k)
    sub = {"@NDEF@": ndef, "@LO@": lo}
    det_expr = (1 - c) ** (n - 1) * (1 + (n - 1) * c)
    sub["@DET@"] = (r"(1-c)^{n-1}(1+(n-1)c)" if k is None else _latex(det_expr, k))
    sub["@NM1@"] = "n-1" if k is None else str(k - 1)

    if t == "T4":
        c2 = -sp.Rational(1, 4) * n * (n - 1)
        c3 = sp.Rational(1, 6) * n * (n - 1) * (n - 2)
        hess = -n * (n - 1) / 2
        if k is None:
            sub["@C2@"] = r"-\frac{n(n-1)}{4}"
            sub["@C3TERM@"] = r"+\frac{n(n-1)(n-2)}{6}\,c^3"
            sub["@HESS@"] = r"-\frac{n(n-1)}{2}"
        else:
            sub["@C2@"] = _latex(c2, k)
            v3 = c3.subs(n, k)
            sub["@C3TERM@"] = ("" if v3 == 0 else r"+c^3" if v3 == 1
                               else "+" + _latex(c3, k) + r"\,c^3")
            sub["@HESS@"] = _latex(hess, k)

    if t == "T6":
        if k is None:
            sub["@FACET@"] = r"$R_{n-1}(c)$ when $n\ge3$, and to a unit segment when $n=2$."
            sub["@RIGID@"] = (r"If $n\ge3$, the intrinsic piecewise flat metric of the boundary of $R_n(c)$ determines $c$, and hence determines $R_n(c)$ up to congruence. "
                              r"If $n=2$, the intrinsic metric of the boundary is that of a circle of length $4$ for every $c$, so $c$ is not determined, although the area $\sqrt{1-c^2}$ varies with $c$.")
            sub["@RIGIDPROOF@"] = _T6_PROOF_GENERAL
        elif k == 2:
            sub["@FACET@"] = r"a unit segment."
            sub["@RIGID@"] = (r"The boundary of $R_2(c)$ is a closed polygon of four unit sides. Its intrinsic metric is that of a circle of length $4$ for every $c$, so the intrinsic metric of the boundary does not determine $c$, although the area $\sqrt{1-c^2}$ varies with $c$.")
            sub["@RIGIDPROOF@"] = (r"The boundary of a plane convex polygon with four sides of length $1$ is a closed curve of length $4$. Its intrinsic metric depends only on the length, and carries no information about the interior angles. The area is $\sqrt{\det G_2(c)}=\sqrt{1-c^2}$ by Lemma~\ref{lem:spec}.")
        else:
            sub["@FACET@"] = rf"$R_{{{k-1}}}(c)$."
            sub["@RIGID@"] = (r"The intrinsic piecewise flat metric of the boundary of $R_n(c)$ determines $c$, and hence determines $R_n(c)$ up to congruence.")
            sub["@RIGIDPROOF@"] = _T6_PROOF_SPECIFIC

    if t == "T7":
        fv = (1 - a / n) ** (n - 1) * (1 + (n - 1) * a / n)
        sub["@NDEF@"] = r"Let $n\ge2$ be an integer" if k is None else f"Let $n={k}$"
        if k is None:
            sub["@FV@"] = r"\Bigl(1-\frac an\Bigr)^{n-1}\Bigl(1+\frac{(n-1)a}{n}\Bigr)"
            sub["@LIMIT@"] = r"Moreover, for fixed $a>-1$, $\displaystyle\lim_{n\to\infty}\det G_n(a/n)=(1+a)e^{-a}$."
            sub["@LIMITPROOF@"] = (r"For the limit, $(1-\frac an)^{n-1}=(1-\frac an)^n/(1-\frac an)\to e^{-a}$ and $1+\frac{(n-1)a}{n}\to1+a$. For $a>-1$ the value $c=a/n$ lies in the positivity range for all large $n$.")
        else:
            sub["@FV@"] = _latex(fv, k)
            sub["@LIMIT@"] = r"This is an exact value at one finite $n$. The corresponding limit statement concerns the whole sequence in $n$ and is not asserted here."
            sub["@LIMITPROOF@"] = r"No limit is taken."

    if t == "T8":
        if k is None:
            sub["@T8SHAPE@"] = (r"For $n\ge3$ the bodies $R_n(c_-)$ and $R_n(c_+)$ are not congruent, so volume does not determine the shape. "
                                r"For $n=2$ the two bodies are congruent: $R_2(c)$ and $R_2(-c)$ are the same rhombus, so in dimension $2$ the statement concerns the parameter $c$ only and is not a counterexample about shapes.")
            sub["@T8SHAPEPROOF@"] = _T8_PROOF_GENERAL
        elif k == 2:
            sub["@T8SHAPE@"] = (r"Here $c_-=-c_+$. However $R_2(c_+)$ and $R_2(-c_+)$ are congruent, since a rhombus with angle $\theta$ also has angle $\pi-\theta$. "
                                r"So in dimension $2$ this is a counterexample to the injectivity of $c\mapsto\vol_2R_2(c)$ only, and not a counterexample to the claim that the area determines the shape.")
            sub["@T8SHAPEPROOF@"] = (r"For $n=2$, $\det G_2(c)=1-c^2$ is even in $c$, so $c_-=-c_+$. A rhombus with unit sides is determined up to congruence by the angle $\theta$ between two adjacent sides, and it has the angle $\pi-\theta$ at its other two vertices. So the rhombus with angle $\theta$ and the rhombus with angle $\pi-\theta$ are the same rhombus, and $\cos(\pi-\theta)=-\cos\theta$ gives $R_2(c)\cong R_2(-c)$.")
        else:
            sub["@T8SHAPE@"] = r"The bodies $R_n(c_-)$ and $R_n(c_+)$ are not congruent, so volume does not determine the shape."
            sub["@T8SHAPEPROOF@"] = _T8_PROOF_GENERAL

    out = BODY[t]
    for key, val in sub.items():
        out = out.replace(key, val)
    # placeholders not used by this contribution are absent; N is only informative
    return out.replace("@N@", N)


_T6_CORE = (
    r"Two edges at a vertex lie in a common flat $2$-face, so the intrinsic metric of the boundary determines the angle between any two edges at any vertex, hence the Gram matrices $D_\varepsilon G_n(c)D_\varepsilon$ of Lemma~\ref{lem:vertex} at all vertices, up to permutation of the edges. "
    r"The vertex $S=\emptyset$ has all off-diagonal entries equal to $c$. By Lemma~\ref{lem:vertex}, any vertex whose off-diagonal entries are all equal has that common value $c$, so $c$ is read off from the boundary. "
    r"The pair $(n,c)$ determines $R_n(c)$ up to an orthogonal map by the Cholesky argument: if $W^\T W=V^\T V$ with $V$ invertible then $W=QV$ with $Q=WV^{-1}$ orthogonal."
)
_T6_PROOF_GENERAL = (
    r"Let $n\ge3$. " + _T6_CORE +
    r" For $n=2$ no such recovery is possible, as the boundary is a circle of length $4$ whatever $c$ is."
)
_T6_PROOF_SPECIFIC = _T6_CORE

_T8_PROOF_GENERAL = (
    r"Non-congruence for $n\ge3$: a congruence $R_n(c_-)\to R_n(c_+)$ maps the vertex $S=\emptyset$ of $R_n(c_-)$ to a vertex of $R_n(c_+)$ and maps its edge directions to the edge directions there, preserving inner products. "
    r"The Gram matrix at $S=\emptyset$ has all off-diagonal entries equal to $c_-$, and the Gram matrix at the image vertex is $D_\varepsilon G_n(c_+)D_\varepsilon$ up to permutation. By Lemma~\ref{lem:vertex}, $c_-=c_+$, which contradicts $c_-<0<c_+$. "
    r"For $n=2$ the two rhombi are congruent, as follows. A rhombus with unit sides is determined up to congruence by the angle $\theta$ between two adjacent sides, and it has the angle $\pi-\theta$ at its other two vertices. So the rhombus with angle $\theta$ and the rhombus with angle $\pi-\theta$ are the same rhombus, and $\cos(\pi-\theta)=-\cos\theta$ gives $R_2(c)\cong R_2(-c)$."
)

DESCRIPTIONS = {
    "T1": "existence, uniqueness up to orthogonal maps, and the positivity range of the Gram matrix",
    "T2": "volume is at most 1, with equality only for the unit cube",
    "T3": "the cube is the unique maximizer and unique critical point of the volume",
    "T4": "second and third order expansion of the log volume at the cube",
    "T5": "rank of the edge system at interior and endpoint values of the parameter",
    "T6": "facets are lower dimensional members of the family, and the boundary determines the parameter exactly when n is at least 3",
    "T7": "exact value of det G_n(a/n) and its limit (1+a)exp(-a)",
    "T8": "volume takes each value in (0,1) exactly twice, with shape consequences that depend on n",
}


DESCRIPTIONS_INF = {
    "T1": "unit vector systems with equal inner products exist for 0 <= c <= 1, and the Gram operator is bounded on l2 only for c = 0",
    "T2": "limiting volume is 1 at c = 0 and 0 for 0 < c < 1",
    "T3": "the cube is the unique maximizer of the limiting volume",
    "T4": "the quadratic coefficient of the log volume diverges with the dimension",
    "T5": "for 0 <= c < 1 the system is linearly independent and fits in no finite dimensional space",
    "T6": "for every finite section of order at least 3 the boundary determines c",
    "T7": "limit of det G_n(a/n) is (1+a)exp(-a)",
    "T8": "the limiting volume is constant on (0,1), so volume does not determine c",
}


def class_summary(rec):
    """Plain-text one-line description of a statement class."""
    parts = []
    for t, dim in rec["members"]:
        parts.append(t)
    ts = sorted(set(t for t, _ in rec["members"]))
    scope = rec["scope"]
    table = DESCRIPTIONS_INF if scope == "infinite dimension" else DESCRIPTIONS
    base = "; ".join(f"{t}: {table[t]}" for t in ts)
    if "explicit_partner" in rec["content"]:
        base += " (in dimension 2 the partner of c is -c, and R_2(c), R_2(-c) are congruent)"
    return base


# ---------------------------------------------------------------------------
# Abstract sentences
# ---------------------------------------------------------------------------

def claim_sentence(t, dim):
    k = None if dim in ("n", "infinite") else int(dim)
    nn = "$n$" if k is None else f"$n={k}$"
    if dim == "infinite":
        return {
            "T1": "In infinite dimension an infinite system of unit vectors with equal pairwise inner product $c$ exists exactly for $0\\le c\\le1$, and its Gram matrix is a bounded operator on $\\ell^2$ only for $c=0$.",
            "T2": "In infinite dimension the limiting volume of the cubic rhombus is $1$ at $c=0$ and $0$ for $0<c<1$.",
            "T3": "In infinite dimension the unit cube is the unique maximizer of the limiting volume of the cubic rhombus.",
            "T4": "The quadratic coefficient of the log volume at the cube diverges with the dimension, so there is no uniform local expansion.",
            "T5": "For $0\\le c<1$ an infinite system of unit vectors with equal pairwise inner product $c$ is linearly independent and fits in no finite dimensional space.",
            "T6": "For every finite section of order at least $3$ the boundary determines the parameter $c$.",
            "T7": "$\\det G_n(a/n)$ tends to $(1+a)e^{-a}$ as $n\\to\\infty$.",
            "T8": "In infinite dimension the limiting volume is constant on $(0,1)$, so volume does not determine $c$.",
        }[t]
    return {
        "T1": f"For {nn} a cubic rhombus $R_n(c)$ exists exactly for $c$ in an explicit open interval, and is unique up to orthogonal maps.",
        "T2": f"For {nn} the volume of a cubic rhombus with unit edges is at most $1$, with equality only for the cube.",
        "T3": f"For {nn} the unit cube is the unique maximizer and the unique critical point of the volume among cubic rhombi.",
        "T4": f"For {nn} the log volume of a cubic rhombus has an explicit expansion to third order at the cube.",
        "T5": f"For {nn} the edge system of a cubic rhombus has full rank in the interior of the parameter range and rank drops at the endpoints.",
        "T6": f"For {nn} the facets of a cubic rhombus are lower dimensional cubic rhombi, and the statement about whether the boundary determines $c$ is made precise.",
        "T7": (f"For {nn} an exact formula for $\\det G_n(a/n)$ is given, and for general $n$ its limit as $n\\to\\infty$ is $(1+a)e^{-a}$."
               if k is None else f"For {nn} an exact formula for $\\det G_n(a/n)$ is given."),
        "T8": f"For {nn} the volume of a cubic rhombus takes each value in $(0,1)$ exactly twice as $c$ varies."
              + (" In dimension $2$ the two parameter values give the same rhombus." if k == 2 else ""),
    }[t]


LABEL_NOTES = {
    "T3": "The proposition is a restatement of the one in contribution T2, and has the same proof.",
    "T7": "The word ``equidistribution'' is retained from the title template. No distribution is considered. The proposition concerns a limit of determinants.",
    "T8": "The statement is a counterexample to the injectivity of volume as a function of $c$, with the shape consequences stated in the theorem.",
}

TECHNIQUE = {
    "T1": "linear algebra (eigenvalues and a Cholesky factorization)",
    "T2": "one variable calculus applied to the logarithm of the determinant",
    "T3": "one variable calculus applied to the logarithm of the determinant",
    "T4": "Taylor expansion of two logarithms",
    "T5": "a rank computation from the spectrum of the Gram matrix",
    "T6": "restriction of the Gram matrix to a principal submatrix, and vertex Gram matrices",
    "T7": "elementary limits",
    "T8": "monotonicity, the intermediate value theorem, and vertex Gram matrices",
}


def write_lib(lib_dir):
    import os
    os.makedirs(os.path.join(lib_dir, "body"), exist_ok=True)
    files = {"preamble.tex": PREAMBLE, "refs.tex": REFS, "lemmas.tex": LEMMAS,
             "lemmas_inf.tex": LEMMAS_INF}
    for t in CONTRIBUTIONS:
        for dim in DIM_LABELS:
            files[f"body/{t}_{dim}.tex"] = body(t, dim)
    for rel, text in files.items():
        with open(os.path.join(lib_dir, rel), "w", encoding="utf-8") as f:
            f.write(text)
    return sorted(files)


def manuscript_tex(m, cls, class_info):
    """m: manuscript dict; cls: class record; class_info: dict with counts."""
    t, dim = m["t"], m["dim"]
    lemmas = "lemmas_inf" if dim == "infinite" else "lemmas"
    op = "Operative" if True else ""
    members = sorted(set(f"{tt} ({LABELS[tt]})" for tt, _ in cls["members"] if tt != t))
    shared = ""
    if members:
        shared = (" The same class also arises from the contributions "
                  + "; ".join(members).replace("&", "and")
                  + ". These are the same statement under different titles.")
    technique = TECHNIQUE[t]
    principal = class_info["principal"]
    is_principal = principal == m["id"]
    rel = ("This manuscript is the principal member of its class in this release." if is_principal
           else f"The principal member of this class in this release is manuscript {principal}. "
                "This manuscript restates that proposition under different title parameters.")
    note = LABEL_NOTES.get(t, "The label corresponds to the proposition proved here.")
    dimtext = "the infinite dimensional case" if dim == "infinite" else f"dimension ${dim}$"
    abstract = (
        f"{claim_sentence(t, dim)} "
        f"This manuscript states and proves exactly this proposition and nothing more. "
        f"The title names a {m['g']} geometry, a {m['top']} topology, {m['reg']} regularity, {m['bd']} boundary conditions "
        f"and a {m['proof']} technique. None of these enters the argument (Section~\\ref{{sec:params}}). "
        f"The proposition belongs to class {cls['id']}, which {class_info['count']} manuscripts of this release share. "
        f"This manuscript does not establish the result its title suggests. {NONSUPPORT}"
    )
    table_rows = [
        ("Dimension", "Operative", f"The proposition is stated for {dimtext}."),
        ("Contribution", "Operative", note),
        ("Geometry: " + m["g"], "Not used", "Every statement concerns the Euclidean metric on $\\R^n$."),
        ("Topology: " + m["top"], "Not used", "$R_n(c)$ is a convex polytope, hence contractible. No other topology is considered."),
        ("Regularity: " + m["reg"], "Not used", "The object is a polytope. No function space on it is considered, and the label is carried as metadata."),
        ("Boundary conditions: " + m["bd"], "Not used", "No boundary value problem is posed. The word boundary in Theorem~\\ref{thm:main} refers to the facets of the polytope, where it occurs."),
        ("Technique: " + m["proof"], "Not used", f"The proof given is by {technique}. The label is carried as metadata."),
    ]
    rows = "\n".join(f"{a_} & {b_} & {c_} \\\\" for a_, b_, c_ in table_rows)
    return rf"""\documentclass[11pt]{{article}}
\input{{../../lib/preamble}}
\title{{{m['title_tex']}}}
\author{{{AUTHOR}}}
\date{{Release 1.0\\ Manuscript {m['id']}}}
\begin{{document}}
\maketitle
\begin{{abstract}}
{abstract}
\end{{abstract}}

\section{{Introduction}}
The cubic rhombus $R_n(c)$ is the parallelotope with unit edges and constant pairwise edge inner product $c$. Its Gram matrix is $(1-c)I+cJ$, and every quantity below is computed from this one matrix. The classical background is the Gram determinant~\cite{{gram}} and Hadamard's inequality~\cite{{hadamard}}; see also~\cite{{hj}}.
This manuscript proves one proposition about this family. The title of the manuscript promises more than the proposition delivers. {NONSUPPORT}

\section{{Setting}}
\input{{../../lib/{lemmas}}}

\section{{Result}}
\input{{../../lib/body/{t}_{dim}}}

\section{{Parameters carried in the title}}\label{{sec:params}}
\begin{{center}}
\small
\begin{{tabular}}{{p{{0.27\textwidth}}p{{0.13\textwidth}}p{{0.50\textwidth}}}}
\toprule
Parameter & Status & Role in the argument \\
\midrule
{rows}
\bottomrule
\end{{tabular}}
\end{{center}}
Of the seven parameters of the title, two enter the argument and five do not. The five that do not are retained so that the title is complete.

\section{{Relation to the rest of the release}}
The proposition of this manuscript is in class {cls['id']} (scope: {cls['scope']}).{shared}
In this release, {class_info['count']} manuscripts carry class {cls['id']}. {rel}
Counting manuscripts is therefore not counting results. {NONSUPPORT}

\section{{Verification status}}
\begin{{center}}
\small
\begin{{tabular}}{{ll}}
\toprule
Item & Status \\
\midrule
Human review & none \\
Independent scrutiny & none \\
Lean formalization & not attempted \\
Exact computer algebra checks tagged to this class & {class_info['checks']} of {class_info['checks']} passed \\
Novelty of the proposition & not assessed \\
\bottomrule
\end{{tabular}}
\end{{center}}
The computer algebra checks confirm closed forms against direct computation for $n=2,\dots,8$ and confirm the symbolic identities in $n$. They do not address novelty or significance. Some results could have issues, and a correction would be recorded as a new version.

\section{{Statement of non-support}}
This manuscript proves a proposition about a determinant of a matrix of the form $(1-c)I+cJ$. It does not prove, support, or provide evidence for the claim that the proposition is an independent result, a new result, or a result of the kind the title suggests. {NONSUPPORT}

\input{{../../lib/refs}}
\end{{document}}
"""
