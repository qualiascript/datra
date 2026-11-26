"""Exercise the dashboard against temporary Git repositories, without network access."""
import datetime as dt
import os
from pathlib import Path
import subprocess
import tempfile
import time
import unittest

from serve import Dashboard, History, ZoneInfo, run


class HistoryTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='datra-loc-test-')
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.repo = self.root / 'repo'
        self.repo.mkdir()
        self.git('init', '-b', 'main')
        self.git('config', 'user.name', 'LOC test')
        self.git('config', 'user.email', 'loc-test@example.invalid')
        self.today = dt.datetime.now(ZoneInfo('America/New_York')).date()
        for directory in ['docs', 'src/DatraCore', 'test', 'app']:
            (self.repo / 'datra-haskell' / directory).mkdir(parents=True)
        self.code = self.repo / 'datra-haskell/app/Main.hs'
        self.code.write_text('a\nb\nc\n')
        for name in ['docs/a.txt', 'src/DatraCore/Core.hs', 'test/Test.hs']:
            (self.repo / 'datra-haskell' / name).write_text('excluded\n' * 100)
        (self.repo / 'datra-haskell/app/blob.bin').write_bytes(b'\x00binary\n')
        self.commit('Initialize implementation', days_ago=7)
        self.history = History(self.repo, self.root / 'cache', 'America/New_York', offline=True)

    def git(self, *args, env=None):
        return subprocess.check_output(['git', '-C', str(self.repo), *args],
                                       stderr=subprocess.DEVNULL, env=env).decode().strip()

    def commit(self, subject, days_ago=0):
        date = (self.today - dt.timedelta(days=days_ago)).isoformat()
        stamp = date + 'T12:00:00-05:00'
        env = dict(os.environ, GIT_AUTHOR_DATE=stamp, GIT_COMMITTER_DATE=stamp)
        self.git('add', '.')
        self.git('commit', '-m', subject, env=env)
        return self.git('rev-parse', 'HEAD')

    def build(self):
        return self.history.build(*self.history.snapshot())

    def squash_feature(self):
        self.git('checkout', '-b', 'feature')
        self.code.write_text('a\nb\nc\nd\n')
        self.commit('First addition', days_ago=2)
        self.code.write_text('a\nb\nc\nd\ne\n')
        head = self.commit('Second addition', days_ago=1)
        self.git('checkout', 'main')
        self.git('merge', '--squash', 'feature')
        self.commit('Feature (#1)')
        run(self.history.g + ['fetch', '--quiet', str(self.repo), head + ':refs/pr/1'])

    def test_exclusions_and_partial_last_line(self):
        self.code.write_text('a\nb\nc')
        (self.repo / 'datra-haskell/app/link.hs').symlink_to('Main.hs')
        self.commit('Partial last line and symlink')
        result = self.build()
        self.assertEqual(result['total'], 3)
        self.assertEqual(result['rows'][-1]['net_loc'], 0)
        self.assertEqual(result['observed_through'], self.today.isoformat())
        self.assertEqual(len(result['rows']), 8)
        self.assertIsNone(result['rows'][5]['rate'])
        self.assertEqual(result['rows'][-1]['rate'], 0)

    def test_squash_changes_are_spread_over_original_days(self):
        self.squash_feature()
        result = self.build()
        self.assertEqual(result['total'], 5)
        self.assertEqual(result['expanded_prs'], 1)
        self.assertEqual(result['original_commits'], 2)
        self.assertEqual([r['net_loc'] for r in result['rows'][-3:]], [1, 1, 0])
        self.assertAlmostEqual(result['rate'], 2 / 7)
        self.assertEqual(result['missing_prs'], [])
        self.assertEqual(result['reconciliations'], [])

    def test_missing_pr_preserves_endpoint_and_reports_merge_day_fallback(self):
        self.code.write_text('a\nb\nc\nd\n')
        self.commit('Addition (#999)')
        result = self.build()
        self.assertEqual(result['total'], 4)
        self.assertEqual(result['rows'][-1]['net_loc'], 1)
        self.assertEqual(result['missing_prs'], [999])
        self.assertTrue(any('#999' in warning for warning in result['warnings']))

    def test_watcher_follows_branches_and_commits_but_ignores_uncommitted_edits(self):
        dashboard = Dashboard(self.history)
        def rebuild():
            dashboard.check()
            deadline = time.monotonic() + 10
            while dashboard.status()['busy'] and time.monotonic() < deadline:
                time.sleep(.01)
            status = dashboard.status()
            self.assertFalse(status['busy'], 'History calculation did not finish')
            self.assertIsNone(status['error'])
            return status['data']
        initial = rebuild()
        self.assertEqual(initial['branch'], 'main')
        self.git('checkout', '-b', 'shrink')
        renamed = rebuild()
        self.assertEqual(renamed['branch'], 'shrink')
        self.assertEqual(renamed['head'], initial['head'])
        self.code.write_text('a\n')
        new_head = self.commit('Remove implementation lines')
        result = rebuild()
        self.assertEqual(result['head'], new_head)
        self.assertEqual(result['total'], 1)
        self.code.write_text('uncommitted\n' * 500)
        unchanged = rebuild()
        self.assertEqual(unchanged['head'], new_head)
        self.assertEqual(unchanged['total'], 1)


if __name__ == '__main__':
    unittest.main()
