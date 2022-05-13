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
        var i := 0;
        while(i < tree.Length) 
        decreases tree.Length - i
        modifies tree
        invariant 0 <= i <= tree.Length
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
    ensures forall j :: (leaves - 1 <= j < 2*leaves-1) ==> if j != (tree.Length)/2 + i then tree[j] == old(tree[j]) 
                else tree[j] == old(tree[j] + v)
    modifies tree
    {
        var m := (tree.Length)/2 + i;
        tree[m] := tree[m] + v;
        while(m > 0)
            decreases m
            invariant 0 <= m <= i + leaves - 1
            invariant forall j :: (leaves - 1 <= j < 2*leaves-1) ==> if j != (tree.Length)/2 + i then tree[j] == old(tree[j]) 
                else tree[j] == old(tree[j] + v)
            invariant forall k :: (0 <= k < leaves - 1) ==> if (k == (m-1)/2) then tree[k] + v == tree[2 * k+1] + tree[2 * k+2] 
                else tree[k] == tree[2 * k+1] + tree[2 * k+2]
        {
            m := (m - 1) / 2;
            tree[m] := tree[m] + v;
        }
    }
    
    //Ranged sum over interval [a,b[
    method query(a: int,b: int) returns (r: int)
    requires 0 <= a <= b <= leaves
    requires Valid()
    ensures Valid()
    ensures r == rsum(a,b)
    {
        r := 0;
        var ra := tree.Length/2 + a;
        var rb := tree.Length/2 + b;
        shift(a,b,leaves-1);
        while(ra < rb)
        decreases rb - ra
        invariant 0 <= ra <= rb <= tree.Length
        invariant r == rsum(a,b) - sumArr(ra, rb)
        {
            if (ra % 2 == 0)
            {
                r := r + tree[ra];
            }
            if (rb % 2 == 0)
            {
                r := r + tree[rb - 1];
            }
            sumArrSwap(ra,rb);
            ra := ra / 2;
            rb := (rb-1)/2;
            crucial(ra,rb);
        }
    }

    //Sum of elements over range [a,b[
    function rsum(a: int,b: int) : int
    requires Valid()
    decreases b-a
    requires 0 <= a <= leaves && 0 <= b <= leaves
    reads this, tree
    {
        if b <= a then 0 else get(b-1)+rsum(a,b-1)
    }

    //sum of array elements in [a,b[
    function sumArr(a: int,b: int) : int
    requires Valid()
    requires 0 <= a <= tree.Length && 0 <= b <= tree.Length
    reads this, tree
    {
        if b <= a then 0 else tree[b-1]+sumArr(a,b-1)
    }

    predicate ValidSize()
    reads this, tree
    {
        tree.Length == 2*leaves-1
    }

    predicate Valid()
    reads this, tree
    {
        ValidSize() &&  forall i :: 0 <= i < leaves - 1 ==> tree[i] == tree[2*i + 1] + tree[2*i + 2]
    }
    
    /*ith element of the sequence, through the array-based
    representation*/
    function get(i: int) : int
    requires 0 <= i < leaves && ValidSize()
    reads this, tree
    {
        tree[i + leaves - 1]
    }

    lemma shift(a: int,b: int,c: int)
    requires Valid() && 0 <= c <= leaves-1
    requires 0 <= a <= leaves && 0 <= b <= leaves
    requires forall i :: a <= i < b ==> get(i) == tree[i+c]
    ensures rsum(a,b) == sumArr(a+c,b+c)
    decreases b-a
    {
        if (b > a) {
            shift(a, b-1, c); 
        }
    }

    lemma crucial(ra: int,rb: int)
    requires 0 <= ra <= rb && 2*rb < tree.Length && Valid()
    ensures sumArr(ra,rb) == sumArr(2*ra+1,2*rb+1)
    {

    }

    lemma sumArrSwap(ra: int,rb: int)
    requires Valid()
    requires 0 <= ra < rb && 0 <= rb <= tree.Length
    ensures sumArr(ra,rb) == tree[ra]+sumArr(ra+1,rb)
    {
        
    }
}

// lemma bruh ()