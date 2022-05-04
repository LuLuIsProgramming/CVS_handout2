class IntervalTree {

    //The actual tree
    var tree: array<int>

    /*The number of leaves in the tree (i.e. the number of elements in
    the sequence). */
    ghost var leaves: int

    /*Initializes an interval tree for a sequence of n elements whose
    values are 0. */
    constructor(n: int)
    requires n > 0
    ensures leaves == n
    ensures ValidSize()
    {
        leaves := n;
        tree := new int[2*(leaves-1)];

    }

    //Updates the i-th sequence element (0-based) by v
    method update(i: int,v: int)
    requires 0 <= i < leaves
    requires ValidSize()
    ensures ValidSize()
    {

    }
    
    //Ranged sum over interval [a,b[
    method query(a: int,b: int) returns (r: int)
    requires 0 <= a <= b <= leaves
    requires ValidSize()
    ensures ValidSize()
    ensures r == rsum(a,b)
    {

    }

    //Sum of elements over range [a,b[
    function rsum(a: int,b: int) : int
    requires ValidSize()
    decreases b-a
    requires 0 <= a <= leaves && 0 <= b <= leaves
    reads this
    {
        if b <= a then 0 else get(b-1)+rsum(a,b-1)
    }

    predicate ValidSize()
    reads this, tree
    {
        tree.Length == 2*leaves-1
    }
    
    /*ith element of the sequence, through the array-based
    representation*/
    function get(i: int) : int
    requires 0 <= i < leaves && ValidSize()
    reads this, tree
    {
        tree[i + leaves - 1]
    }

}

