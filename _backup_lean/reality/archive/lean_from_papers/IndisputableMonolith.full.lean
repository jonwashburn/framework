/-!
  IndisputableMonolith root aggregator.

  This module exists to support CI quick checks that parse the head of the
  monolith and ensure the toolchain is wired. Keep the imports intentionally
  lightweight and stable.
-/

import IndisputableMonolith.Core
import IndisputableMonolith.Constants
import IndisputableMonolith.Patterns
import IndisputableMonolith.Streams
import IndisputableMonolith.Recognition
import IndisputableMonolith.URCAdapters
import IndisputableMonolith.URCGenerators
import IndisputableMonolith.Verification

-- End of aggregator; extend with additional stable imports as needed.
