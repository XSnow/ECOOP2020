# ECOOP2020 Artifacts

A Type-Directed Operational Semantics

For a Calculus with a Merge Operator

- [coq/](./coq) for Coq formalization of the calculus
- [spec/](./spec) for ott specification of the calculus
- [paper.pdf](./paper.pdf) for the accepted version of paper with appendices

You can also use Docker to get and run the container including the artifact and dependencies by
executing the following command in you machine with Docker installed:

   ```sh
   docker run -it sxsnow/ecoop2020
   ```
   
Ott, LNgen and vim have been set up in the docker image sxsnow/ecoop2020:ott. You can run the following line to create a container by it.

   ```sh
   docker run -it --name ecoop-new sxsnow/ecoop2020:ott
   ```
   
In coq/main_version or coq/variant directory, run

   ```sh
   make ottclean
   ```
   
to remove the generated code, then you can use make to call Ott and LNgen to regenerate them.
