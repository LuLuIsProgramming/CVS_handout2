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
    ensures Valid()
    {
        leaves := n;
        tree := new int[2*n-1];
        new;
        var i := 1;
        tree[0] := 0;
        while(i < tree.Length) 
        decreases tree.Length - i
        invariant 1 <= i <= tree.Length
        invariant forall j :: 0 <= j <i ==> tree[j] == 0

        {
            tree[i] := 0;
            i := i + 1;
        }

    }

    //Updates the i-th sequence element (0-based) by v
    method update(i: int,v: int)
    requires 0 <= i < leaves
    requires Valid()
    ensures Valid()
    modifies tree
    {
        var m := (tree.Length + 1)/2 + (i-1);
        while(m > 0)
            invariant 0 <= m <= i + leaves - 1
            //invariant if m < old(m)  then tree[m] == old(tree[m]) else tree[m] == old(tree[m])+v
            invariant forall j :: (0 <= j < 2*leaves-1 && j != old(m)) ==> tree[j] == old(tree[j])
            
        {
            tree[m] := tree[m] + v;
            m := ((m - 1) / 2);
        }
        tree[0] := tree[0] + v;
    }
    
    //Ranged sum over interval [a,b[
    method query(a: int,b: int) returns (r: int)
    requires 0 <= a <= b <= leaves
    requires Valid()
    ensures Valid()
    ensures r == rsum(a,b)
    {

    }

    //Sum of elements over range [a,b[
    function rsum(a: int,b: int) : int
    requires Valid()
    decreases b-a
    requires 0 <= a <= leaves && a <= b <= leaves
    reads this, tree
    {
        if b <= a then 0 else get(b-1)+rsum(a,b-1)
    }

    predicate ValidSize()
    reads this, tree
    {
        tree.Length == 2*leaves-1
    }

    predicate Valid()
    reads this, tree
    {
        ValidSize() && if leaves == 1 then true else (forall i :: 0 <= i < leaves - 1 ==> tree[i] == tree[2*i + 1] + tree[2*i + 2])
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

