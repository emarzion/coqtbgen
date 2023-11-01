## How to play the game

The game consists of three hunters and one bear placed on a board. At each turn, the player selects a piece and moves it to an open adjacent position on the board. The hunters achieve victory when they have surrounded the bear so that it cannot move.

One can read more about this type of game [here](https://en.wikipedia.org/wiki/Bear_games).

## How to use the tablebase frontend

The frontend displays the current state of the board, with the three hunters represented by white pieces, and the bear represented by a black piece.

There are three modes which the user can toggle between:

  * **Query:** This displays the tablebase result for the current position, along with the results for each possible move.  The user can advance a move by either clicking on a piece to select it, and then clicking on its destination, or by clicking on a move from the list. The naming scheme for moves is as follows:  A bear move is given as **B**_[pos]_ where _[pos]_ denotes the bear's destination.  A hunter move is given as **H**_[pos1][pos2]_ where _[pos1]_ denotes the hunter's origin and _[pos2]_ denotes the hunter's destination. Notations for positions are given by the following diagram:
    <p align="center">
    <img src="https://github.com/emarzion/coqtbgen/assets/18229438/d2b0e5bb-8967-466f-bcb5-0863c6c8af87" width="500" height="500">
    </p>
  * **Edit:** This provides an interface for the user to edit positions by toggling which player's turn it is, and by moving pieces on the board.  Pieces can be moved by clicking on a piece to select it, and then clicking on its destination.
  * **Play:** This allows the user to play the current position against the tablebase.  At the start, the user selects which color they will play as, after which moves will alternate between the user and the tablebase.  When it is their turn, the user can make a move by clicking on a piece to select it, and then clicking on its destination.
