# reasonEq

Theorem prover supporting general equational reasoning,
as well as common idioms used in Unifying Theories of Programming.

## Installation

### Prerequisites

You need to install `stack`.

See <https://docs.haskellstack.org/en/stable/README/>. You are strongly advised to follow their advice regarding the PATH environment variable at <https://docs.haskellstack.org/en/stable/install_and_upgrade/#path>.

### Installing

1. Clone the github repository at a suitable location

`git clone https://github.com/andrewbutterfield/reasonEq.git`

2. Enter the directory `reasonEq'

3. Give command `stack install` and wait. The first time you run this might take a while as it may install a local version of the Haskell compiler and required libraries. When it is done it will have installed a program called `req`.

## Running `reasonEq`/`req`

For new users, we recommend the following procedure:

### First time

1. Select a parent directory to contain your first proof workspace folder.
2. Run the application from within that parent directory using `req`.
3. The program will start, and will create two directories, one that stores user data about your workspaces, and the second one, in your chosen parent directory, being a workspace folder called `MyReasonEq`. All your work will be saved in this folder.
4. It will then start its command-line interface.

### Second and subsequent times

Simply typing `req` anywhere will open the application, with the `MyReasonEq` directory as the current workspace.

## Using `req`

General help can be obtained by typing `help` or `?` at the command prompt. 
This will list the available commands. Typing `help` or `?` followed, after a space, by a command name
will give more details about that command.

The program will automatically save your work on exit, however you can save at anytime with the `save` command.

### Second and subsequent times

Once started for the second time or subsequent times, your current workspace will be automatically loaded.
Use `sh L` to confirm that you have got the right laws and conjectures loaded up.

### Doing Proofs

This is, of course, the whole point of `reasonEq`!

We support having multiple proofs on the go at once, and it is possible to exit the program
mid-proof(s) and still find them ready and waiting for further work when you restart the application.
At any point in time it is only possible to actually be working on one of these "live" proofs at a time,
using a special proof command-line tool.

There are two commands for proofs at the top level, of for starting new proofs (`N`), and the other
for resuming working on an existing proof (`r`).

A tutorial introduction to using the prover is provided in `TUT.pdf` at the repo top-level.
