import Executable.Atlas.Merge.Transport

namespace Datra.Executable.AtlasMerge

-- ALIGN: MERGE-RAW-DATA-INSERTION.
def rawDataMap {Scope : Type} {owner : Scope} (X Y : Atlas)
    {source target : PageElement owner} (arrow : PageElement.Arrow source target)
    (sourceValid : rawTraceValid X Y source) (targetValid : rawTraceValid X Y target)
    (sourceCell targetCell : PageElementCell) :
    DomanialInsertion
      (AcceptedDatum (resolvedContains X Y source : Datum sourceCell → Bool))
      (AcceptedDatum (resolvedContains X Y target : Datum targetCell → Bool)) :=
  acceptedInsertion (resolvedContains X Y source) (resolvedContains X Y target)
    (fun datum accepted => resolvedContains_preserved X Y arrow sourceValid targetValid datum accepted)

end Datra.Executable.AtlasMerge
