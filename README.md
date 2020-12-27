# ECOOP2020 A Type-Directed Operational Semantics for a Calculus with a Merge Operator (Artifact)

- [coq/](./coq) for Coq formalization of the calculus
- [spec/](./spec) for ott specification of the calculus
- [paper.pdf](./paper.pdf) for the camera-ready version of paper with appendices

The instructions and documentation about the Coq code can be found in the [coq](./coq) directory.


## For more information

- A 15-minute conference video can be found [here](https://youtu.be/LGqrXowiSC8).

- A 3-minute poster video can be found [here](https://youtu.be/QFE7kiFXw54).

- Our paper and its BibTex entry can be found on [DROPS](https://drops.dagstuhl.de/opus/volltexte/2020/13183/).

- The artifact and its document can be also found on [DROPS](https://drops.dagstuhl.de/opus/volltexte/2020/13206/).


## Use Docker to get and run it

You can also use Docker to get and run the container including the artifact and dependencies by
executing the following command in your machine with Docker installed:

   ```sh
   docker run -it sxsnow/ecoop2020
   ```
   
Ott, LNgen and Vim have been set up in the docker image. The password for `sudo` is `ecoop2020`.
   
In [coq/main_version](./coq/main_version) or [coq/variant](./coq/variant) directory,
run `make` to build and compile the proofs.

You can also run

   ```sh
   make ottclean
   ```
   
to remove the generated code, then use `make` to call Ott and LNgen to regenerate them.
