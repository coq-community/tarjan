{ coq, mkCoqDerivation, mathcomp-ssreflect, mathcomp-fingroup,
  lib, version ? null }@args:
with lib; mkCoqDerivation {

  namePrefix = [ "coq" "mathcomp" ];
  pname = "tarjan";

  owner = "CohenCyril";

  inherit version;
  defaultVersion = null;
  release = { };

  propagatedBuildInputs = [ mathcomp-ssreflect mathcomp-fingroup ];

  meta = {
    description = "Proofs of Tarjan and Kosaraju connected components algorithms";
    license = licenses.cecill-b;
  };
}
