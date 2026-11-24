import GravitonCert.Core.Boundary
import GravitonCert.Core.Inspect
import GravitonCert.Studies.TimelessGravity
import GravitonCert.Studies.SpinChemistry
import GravitonCert.Studies.ObservationWindow

namespace GravitonCert

/-- Master registry of all certified Graviton Research Foundation studies. -/
def allStudies : List StudyCertificate := [
  Studies.TimelessGravity.studyCertificate,
  Studies.SpinChemistry.studyCertificate,
  Studies.ObservationWindow.studyCertificate
]

end GravitonCert
