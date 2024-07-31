# acl2-experiment
ACL2 experiments on arithmetic circuits

## Experimental

The code here is pure experiment. Don't expect it to be maintained.

## Is this cutting-edge?

No. This is just an experiment using [an existing library](https://www.cs.utexas.edu/~moore/acl2/manuals/current/manual/index-seo.php/R1CS____R1CS) in an elementary way. For more advanced usage of the library see [the paper by the original authors of the library](https://arxiv.org/abs/2311.08858).

## Where is the theorem?

[Here](https://github.com/nexus-xyz/acl2-experiment/blob/64f8951ca3af80da72db680fe6ca23a34875ac91/add32.lisp#L258). It says some conditions about constraints imply [add32p](https://github.com/nexus-xyz/acl2-experiment/blob/64f8951ca3af80da72db680fe6ca23a34875ac91/add32.lisp#L112).

## How to reproduce

1. [Install acl2](https://www.cs.utexas.edu/~moore/acl2/current/HTML/installation/installation.html). The code was developed using the ACL2 commit ID [17138a64970a2ec5159c36d0dcedbba3cb0e3583](https://github.com/search?q=repo%3Aacl2%2Facl2+17138a64970a2ec5159c36d0dcedbba3cb0e3583&type=commits). Build books using `make regression` (or later by need when you get stuck).
2. Run `saved_acl2`
3. Paste the contents of `package.lsp` in this directory into the ACL2 console.
4. Paste the contents of `add32.lisp` in this directory into the ACL2 console.
