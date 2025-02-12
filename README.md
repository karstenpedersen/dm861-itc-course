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



