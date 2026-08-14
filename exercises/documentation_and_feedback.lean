/-!
# Complex Numbers Project: Summary and Course Feedback

## 1. Project Summary
I have tried to build the project from scratch so the project describes complex numbers 
as ordered pairs of real numbers and the I have develeoped some algebraic and geometric properties.

The project contains the following parts:

1. Defining complex numbers as pairs of real numbers.
2. Defining addition, subtraction, multiplication and scalar multiplication.
3. Proving the basic algebraic properties of these operations.
4. Developing complex conjugation, squared length and inverses.
5. Interpreting multiplication by `i` as a quarter-turn rotation.
6. Studying circles and showing that rotations preserve squared length.
7. Introducing the trigonometric form `cis θ`.
8. Working with natural powers and proving De Moivre’s theorem.
9. Factoring and solving the fourth-root equation.
10. Classifying the fourth roots of unity as `1`, `-1`, `i` and `-i`.

Mathlib already contains the type `ℂ` and a complete theory of complex numbers. However, I intentionally reconstructed the elementary definitions because I wanted to understand how the theory could be built from its basic components. I later defined `ascomplex` to connect my construction with Mathlib’s complex numbers.

## Formalisation of the project
1. I started by defining the structure `cnum`, with 2 real-number feilds called `re` and `im`. Any value of this structure represents the complex number `re + im i`.

2. I defined a few special complex numbers such as `zero`, `one` and `ii`. Then I defined Addition, negation, subtraction, multiplication and scalar multiplication directly using their coordinate formulas.

3. I did the algebraic proofs by splitting a complex number into real and imaginary parts. After that, I used tactics such as `simp`, `ring` and `nlinarith` to prove the real-number identities.

4. I defined conjugation by changing the sign of the imaginary component. 

5. Using that then, I also defined the squared norm as `re² + im²`. Using this definition, I proved that the squared norm is non-negative and is zero exactly when both coordinates are zero. I used this to then define and verify the formula for the inverse of a nonzero complex number.

6. For the geometric proofs, multiplication by `ii` was defined as a quarter-turn. I computed the coordinates to show that it sends `(a,b)` to `(-b,a)`. I also proved that this operation preserves the squared norm and also keeps points on the same circle centred at the origin.

7. I have divided the fourth-root classification into smaller results. 
i.) I defined the square and fourth power of a complex number. I then used the factorisation 
`z⁴ - 1 = (z² - 1)(z² + 1)`.

ii.) I proved that the product of 2 complex numbers can be zero only when one of the factors is 0. This reduces the problem to solving `z² = 1` and `z² = -1`. The coordinate equations from these 2 cases give the 4 possible roots `1`, `-1`, `i` and `-i`.

iii.) For the trigonometric part, I defined `cis θ = cos θ + i sin θ` and used `ascomplex` to view it as a Mathlib complex number. I also added the power-series expressions for the exponential, cosine and sine functions.

iv.) I have used existing Mathlib results for the convergence and values of these series. I have separated the exponential series into even and odd terms to get the Euler’s identity
`exp(iθ) = cos θ + i sin θ`.

v.) I did not prove all the convergence results from first principles again. Instead of that, I have used the relevant Mathlib theorems and connected them to my definitions.

vi.) I used Euler’s identity, induction on the natural exponent and `Complex.exp_add` to prove De Moivre’s theorem.

## How I have used Sheets 1–7 and connected my project to the sheets
1. Sheet 1: introduced quantifiers, basic proof tactics and propositions. I have used `intro`, `constructor`, `rcases` throughout my project.

2. Sheet 2: introduced divisibility, finite sets and induction. This sheet was about number theory but I used the method of how to break a bigger proof into smaller statements and used it as a part of my project.

3. Sheet 3: developed prime factorisation, prime exponents, gcd and lcm. Through this sheet, I learned how to create and prove helper lemmas before attempting the main result and I have applied the same learning through out my project. I have created multiple helper lemmas to prove my main theorems. 

4. Sheet 4: introduced quotient types, modular arithmetic, equivalences and bijections. I felt that this was basically one of the more abstract parts of the course but it helped me become very comfortable with structures and functions.

5. Sheet 5: introduced convergence, Cauchy sequences and explicit epsilon arguments. It helped me understand how much detail could be hidden in an informal analysis proof.

6. Sheet 6: mainly developed limit laws, continuity and completeness. The longer proofs that we did in this sheet were very useful while I was preparaing and organising the power-series and exponential part of my project.

7. Sheet 7 introduced derivatives, extrema, Rolle’s theorem and the mean value theorem. Through this sheet, I learned that a large theorem can be constructed from several earlier lemmas and how algebraic, logical and analytic arguments can be combined together.

While I used the techniques that I learned in the earlier sheets to formalise the elementary algebraic part of my project. I required additional Mathlib results so I had to thoroughly explore Mathlib. I had to apply some independent learning and go beyond the direct content of Sheets 1–7 to comeplete the power-series and Euler-identity section. Additionally, my mentor Felix's constant guidance and suggestions were what helped me in finalising the power-series and Euler-identity. 

## General feedback on the course
I found the overall flow of the course useful and extremely structured. It began with building logic and basic Lean syntax, moved through number theory and quotient constructions, and then introduced sequences, continuity and differentiation. This made it possible to see how the same proof techniques are used in different areas of mathematics.

We usually discussed the logic and the math that was needed to construct the proofs in the lecture sessions and we would go over the examples and building materials during our lecture sessions. We were given the opportunity to disvuss and ask doubts and the sessions were extremely interactive.

During the problem solving sessions we asked doubts about the sheets that were due the coming week and also discuss the previously submitted sheets that gave us the opportunity to learn a different way of looking at the problems. 

Once the sheets were submitted, we received an elaborate feedback on our work. The feedback was created in a way that seemed leass judgemental of our performance and enhanced our learning. Felix gave us the opportunity to explore proofs in different ways. he ensured that we aligned our work with the learning from the previous session to ensure that we understood the concepts taught in the class. 

1. Sheets 1 and 2 were a helpful way of introducing Lean to us as the underlying mathematics was familiar and not diffuclt. This allowed me to concentrate on understanding lean, proof writing and tactics.

2. Sheets 3 and 4 were a major jump and considerable increase in difficulty. Prime factorisation mainly involved finding the correct already existing results, while quotient types involved more abstract objects and several coercions. These sheets were quite challenging considering our learning at that point, but they also helped us understand why the exact types of definitions and theorems matter in Lean.

3. Sheet 5 was quite a useful and interesting transition from discrete mathematics to analysis. Writing the epsilon arguments formally helped us in understanding and making the logical structure of convergence clearer.

4. I found Sheet 6 to be the biggest technical jump. Although the math used in the sheet was understandable, but implementing such long arguments that involved continuity, and recursively constructed objects required me to understand how to organise proofs.

5. Sheet 7 helped us combine earlier ideas together. The proofs of Rolle’s theorem and the mean value theorem showed how we can use a sequence of carefully written helper lemmas to get a larger math result.

Difficulties: One of the main difficulties that I faced throughout the course was finding the correct Mathlib theorem and matching its exact statement. Although, Felix was extremely approachable and I reached out to him multiple times during the course to understand how to proceed. Coercions between natural numbers, integers and real numbers were also sometimes difficult to understand from the error messages.

I think I needed some guidnace on using `#check`, `exact?`, `apply?`, `simp?`. It also found it difficlult to read and resolve a complicated type-mismatch error.

The jump to the longer sheets felt a bit challenging. 1 or 2 additional intermediate exercises could help bridge that gap. Although Felix had added some great comments that inclided the entire flow of the theorem in steps. The short written guided steps really made it easy to follow and understand wheteher we were going correct or not.

Overall, the course helped me understand the difference between knowing why a theorem is true informally and specifying every part of its proof precisely. The independent project was especially useful because it required me to choose definitions, organise lemmas and decide when to reconstruct an idea myself and when to use an existing Mathlib result.

It was in every sense a great learning experience and I am so glad that I got to be a part of the course. 

## Vote of Thanks
I would like to express my sincere gratitude to Felix for making this course such an enjoyable learning experience. He was extremely approachable throughout the course and always encouraged us to ask questions. He responded promptly to emails and provided detailed feedback on GitHub, which helped me recognise my mistakes and improve the quality of my proofs. His patience, supportive and non-judgemental approach made the sessions more engaging and fun. We had some great sessions on discord where he helped us with previous submissions that gave us insight into how to think differently about the exercises. I am extremely grateful for the time and effort he put into helping us learn.

-/
