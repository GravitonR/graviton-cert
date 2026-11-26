import GravitonCert.Core.Boundary
import GravitonCert.Core.Inspect
import GravitonCert.Core.Interval
import GravitonCert.Studies.TimelessGravity
import GravitonCert.Studies.PageWootters
import GravitonCert.Studies.SpinChemistry
import GravitonCert.Studies.CircadianTiming
import GravitonCert.Studies.ObservationWindow
import GravitonCert.Studies.NullConeGravity

namespace GravitonCert

/-- Master registry of all certified Graviton Research Foundation studies. -/
def allStudies : List StudyCertificate := [
  Studies.TimelessGravity.studyCertificate,
  Studies.PageWootters.studyCertificate,
  Studies.SpinChemistry.studyCertificate,
  Studies.CircadianTiming.studyCertificate,
  Studies.ObservationWindow.studyCertificate,
  Studies.NullConeGravity.studyCertificate
]

end GravitonCert
