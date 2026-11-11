"""The source browser reads reviewed private and public attribution schemas."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from build_site import pi1_provenance, SourceError

class ProvenanceSchemaTests(unittest.TestCase):
    def test_reviewed_schemas_retain_records_and_reject_duplicates(self):
        base=Path(__file__).resolve().parents[2]/'tmp/site-provenance-tests'
        base.mkdir(parents=True,exist_ok=True)
        with tempfile.TemporaryDirectory(dir=base) as tmp:
            root=Path(tmp); path=root/'Nyll/EtaleFundamentalGroups/Pi1/UPSTREAM.json'
            path.parent.mkdir(parents=True)
            row={'path':'Nyll/Example.lean','role':'nyll_extension'}
            for schema in ('nyll.pi1.provenance.v1','nyll.pi1.provenance.public-extract.v1'):
                data={'schema':schema,'local_source_snapshot':{'files':[row]}}
                path.write_text(json.dumps(data))
                self.assertEqual(pi1_provenance(root),{row['path']:row})
                data['local_source_snapshot']['files'].append(row)
                path.write_text(json.dumps(data))
                with self.assertRaisesRegex(SourceError,'Duplicate pi1'):
                    pi1_provenance(root)
            path.write_text(json.dumps({'schema':'unreviewed','local_source_snapshot':{'files':[row]}}))
            with self.assertRaisesRegex(SourceError,'Unsupported pi1'):
                pi1_provenance(root)
