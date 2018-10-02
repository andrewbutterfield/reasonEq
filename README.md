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
3. The program will start, and will create two directories, one that stores user data about your workspaces, and the second one, in your chosen parent directory, being a workspace folder called `MyReasonEq'. All your work will be saved in this folder.
4. It will then start its command-line interface.

### Second and subsequent times

Simply typing `req` anywhere will open the application, with the `MyReasonEq` directory as the current workspace.

## Using `req`

### First time

At present, you need to install some builtin theories to get going.
Give the command `help b` to find out about builtin theories, and try to install some of them.

Use the `sh L` command to see what laws and conjectures are available as you do this.

When finished, give the `save` command before you `quit`.

At present, there is no auto-save, or checking if anything has been modifed but not saved. So be careful.

### Second and subsequent times

Once started, give the `load` command to get what was saved in the current workspace. Use `sh L` to confirm that you have got the right laws and conjectures loaded up.

At present there is no auto-load of the workspace.

### Doing Proofs

This is, of course, the whole point of `reasonEq`.

Instructions to follow, but for now, start by giving the command `? and see where it takes you.
