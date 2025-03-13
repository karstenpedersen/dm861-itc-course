# DM861 Concurrency Theory

Welcome to the GitHub repository for the course DM861 Concurrency Theory held at the University of Southern Denmark!

# Get ready

## Install Lean 4
- Prerequisite: to install VS Code.
- Follow the official instructions to setup Lean 4: https://docs.lean-lang.org/lean4/doc/quickstart.html
- If you have issues installing Lean using the offical instructions, you can also refer to the platform-specific instructions: https://leanprover-community.github.io/get_started.html

## Build this repository
- Clone this repository from GitHub using either https:

    `git clone https://github.com/chords-project/itc-course.git`

    or ssh

    `git clone git@github.com:chords-project/itc-course.git`
- Enter the `itc-course/` directory.
- Download available pre-compiled caches (this speeds up the next step, building):

    `lake exe cache get`
- Proceeding to building the project using `lake`:

    `lake build`
- Building the project may take some time. Once the process is successfully completed, you can execute the code using the following command:

    `.lake/build/bin/itc-course`

    It should print `Hello, world!`.

# Hacking in Lean 4
Here are useful materials for learning theorem proving in Lean 4.
- [Basic] Learning the basic tactics in Lean 4 via a game: [The Natural Number Game](https://adam.math.hhu.de/#/g/leanprover-community/nng4)
- More on tactics:
    - To list all tactics in Lean4
    ```lean
        import Mathlib.Tactic.HelpCmd
        #help tactic 
    ```
    - A list of all tactics in Lean4 can also been found [here](https://github.com/haruhisa-enomoto/mathlib4-all-tactics/blob/main/all-tactics.md)
- Lean 4 and Mathlib 4 documentation: [link](https://leanprover-community.github.io/mathlib4_docs/index.html)
- [Advanced] Aesop -- proof automation: 
    - [GitHub](https://github.com/leanprover-community/aesop)
    - [Aesop: White-Box Best-First Proof Search for Lean (CPP 23)](https://dl.acm.org/doi/10.1145/3573105.3575671)

