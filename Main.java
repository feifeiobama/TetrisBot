import java.util.*;
import java.util.function.*;
import java.util.stream.*;
import static java.lang.Math.*;

public class Main {
    static class Args {
        static final double BlkC = 4.0, PosC = 2.0;
        static final double[] Arg = {1.00, 0.29};
        static final double Dead = 100.0;
        static final long Clk = System.nanoTime() + 2500_000_000L;
    }
    static class Rule {
        static final int W = 10, H = 20, R = 4, T = 7, P = 800;
        private static final int[][][] Masks =
            { { {0b111, 0b1}, {0b1, 0b1, 0b11}, {0b100, 0b111}, {0b11, 0b10, 0b10} },
              { {0b111, 0b100}, {0b11, 0b1, 0b1}, {0b1, 0b111}, {0b10, 0b10, 0b11} },
              { {0b110, 0b11}, {0b1, 0b11, 0b10}, {0b110, 0b11}, {0b1, 0b11, 0b10} },
              { {0b11, 0b110}, {0b10, 0b11, 0b1}, {0b11, 0b110}, {0b10, 0b11, 0b1} },
              { {0b10, 0b111}, {0b10, 0b11, 0b10}, {0b111, 0b10}, {0b1, 0b11, 0b1} },
              { {0b1, 0b1, 0b1, 0b1}, {0b1111}, {0b1, 0b1, 0b1, 0b1}, {0b1111} },
              { {0b11, 0b11}, {0b11, 0b11}, {0b11, 0b11}, {0b11, 0b11} } };
        static final Block[] Blocks = {
            new Block(1, 1, 2, 1, Masks[0], 4),
            new Block(1, 1, 2, 1, Masks[1], 4),
            new Block(1, 1, 2, 1, Masks[2], 2),
            new Block(1, 1, 2, 1, Masks[3], 2),
            new Block(1, 0, 2, 1, Masks[4], 4),
            new Block(0, 1, 0, 3, Masks[5], 2),
            new Block(1, 0, 1, 1, Masks[6], 1)
        };
        static final int[] bonus = {0, 1, 3, 5, 7};
    }

    static class Block {
        private int postures;
        private int[] lowerX, lowerY, upperX, upperY, lenthY;
        private int[][] mask;
        int[] board, fceil;

        Block(int x0, int y0, int x1, int y1, int[][] mask, int postures) {
            this.lowerX = new int[] {- x0, y0 - y1, x0 - x1, - y0};
            this.lowerY = new int[] {- y0, - x0, y0 - y1, x0 - x1};
            this.upperX = new int[] {x1 - x0, y0, x0, y1 - y0};
            this.upperY = new int[] {y1 - y0, x1 - x0, y0, x0};
            this.lenthY = new int[]{y1, x1, y1, x1};
            this.mask = mask;
            this.postures = postures;
            initializeStreamProvider();
        }
        static int toX(int p) { return p / (Rule.H * Rule.R); }
        static int toY(int p) { return p / Rule.R % Rule.H; }
        static int toR(int p) { return p % Rule.R; }

        private void initializeStreamProvider(){
            Function<IntFunction<IntPredicate>, int[]>
            genrt = f -> {
                IntStream.Builder b = IntStream.builder();
                IntStream.range(0, 4).forEach(r ->
                    IntStream.range(- lowerX[r], Rule.W - upperX[r]).forEach(x ->
                        idexy.apply(r).filter(f.apply(r)).forEach(y ->
                            b.accept(x * Rule.H * Rule.R + y * Rule.R + r))));
                return b.build().toArray();
            };
            board = genrt.apply(r -> (y -> true));
            fceil = genrt.apply(r -> (y -> y == Rule.H - upperY[r] - 1));
        }
        IntFunction<IntStream>
            lines = r -> IntStream.rangeClosed(0, lenthY[r]),
            idexy = r -> IntStream.range(- lowerY[r], Rule.H - upperY[r]);
        IntPredicate
            nextX = p -> p + Rule.H * Rule.R < Rule.P,
            lastX = p -> p - Rule.H * Rule.R >= 0,
            nextY = p -> toY(p) < Rule.H - 1,
            lastY = p -> toY(p) >= 1,
            withR = p -> toR(p) < postures;
        BiFunction<Integer, Integer, IntUnaryOperator>
            index = (y, r) -> (i -> y + upperY[r] - i),
            fmask = (x, r) -> (i -> mask[r][i] << (x + lowerX[r]));
        Function<int[], IntPredicate>
            avail = line -> (p -> lines.apply(toR(p)).allMatch(i -> {
                int idex = index.apply(toY(p), toR(p)).applyAsInt(i),
                    mask = fmask.apply(toX(p), toR(p)).applyAsInt(i);
                return (line[idex] & mask) == 0;
            }));
    }

    static class Board {
        static class PlayerBoard implements Cloneable {
            private int[] used = new int[Rule.T], line = new int[Rule.H];
            private int[] mask = null;
            private Block curr, next;
            int[] cache;
            int score = 0;

            void setInitType(int id) { ++used[id]; curr = Rule.Blocks[id]; }
            void setType(int id) { ++used[id]; next = Rule.Blocks[id]; }
            void placeBlock(int x, int y, int r) {
                List<Integer> full = new ArrayList<Integer>();
                curr.lines.apply(r).forEach(i -> {
                    int index = curr.index.apply(y, r).applyAsInt(i),
                        fmask = curr.fmask.apply(x, r).applyAsInt(i);
                    if ((line[index] | fmask) == (1 << Rule.W) - 1) {
                        full.add(0, line[index]);
                        System.arraycopy(line, index+1, line, index, Rule.H-index-1);
                        line[Rule.H - 1] = 0;
                    } else { line[index] |= fmask; }
                });
                cache = full.stream().mapToInt(i -> i).toArray();
                score += Rule.bonus[cache.length];
            }
            boolean transfer() {
                curr = next;
                if (cache.length == 0) return false;
                boolean over = Arrays.stream(line, Rule.H - cache.length, Rule.H)
                    .max().getAsInt() != 0;
                System.arraycopy(line, 0, line, cache.length, Rule.H - cache.length);
                System.arraycopy(cache, 0, line, 0, cache.length);
                return over;
            }

            int[] availBlock() {
                int min = IntStream.of(used).min().getAsInt();
                return IntStream.range(0, Rule.T)
                    .filter(i -> used[i] < min + 2).toArray();
            }
            void calcMask() {
                mask = new int[Rule.H + 1];
                IntStream.rangeClosed(1, Rule.H).map(i -> Rule.H - i)
                    .forEach(i -> mask[i] = mask[i + 1] | line[i]);
            }
            int[] availPos() {
                boolean[] avail = new boolean[Rule.P], dfsav = new boolean[Rule.P];
                IntStream.of(curr.board).forEach(p -> 
                    avail[p] = curr.avail.apply(line).test(p));
                IntConsumer[] dfs = new IntConsumer[1];
                dfs[0] = p -> {
                    if (!avail[p] || dfsav[p]) return;
                    else dfsav[p] = true;
                    if (curr.nextX.test(p)) dfs[0].accept(p + Rule.H * Rule.R);
                    if (curr.lastX.test(p)) dfs[0].accept(p - Rule.H * Rule.R);
                    if (curr.nextY.test(p)) dfs[0].accept(p + Rule.R);
                    if (curr.lastY.test(p)) dfs[0].accept(p - Rule.R);
                    dfs[0].accept((p / Rule.R) * Rule.R + (p + 1) % Rule.R);
                };
                if (mask == null) calcMask();
                IntStream.of(curr.fceil).filter(p -> curr.avail.apply(mask).test(p))
                    .forEach(p -> dfs[0].accept(p));
                return IntStream.of(curr.board).filter(p -> curr.withR.test(p) &&
                    dfsav[p] && !(curr.lastY.test(p) && dfsav[p - Rule.R])).toArray();
            }
            double evaluate() {
                if (mask == null) calcMask();
                return Args.Arg[0] * IntStream.range(0, Rule.H)
                           .filter(i -> (mask[i] & ~line[i]) != 0).count()
                     + Args.Arg[1] * IntStream.of(mask)
                           .map(x -> (int) IntStream.rangeClosed(0, Rule.W - 1)
                               .map(i ->(((x + (1 << Rule.W)) << 1) + 1) >> i)
                               .filter(y -> (y & 7) == 5).count()).sum();
            }

            protected PlayerBoard clone() throws CloneNotSupportedException {
                PlayerBoard p = (PlayerBoard) super.clone();
                p.used = used.clone();
                p.line = line.clone();
                p.mask = null;
                return p;
            }
        }
        private PlayerBoard[] opBoard = {new PlayerBoard(), new PlayerBoard()};

        void swapCache() {
            int[] cache = opBoard[0].cache;
            opBoard[0].cache = opBoard[1].cache;
            opBoard[1].cache = cache;
        }
        Board read() {
            Scanner in = new Scanner(System.in);
            int[] info = new int[4];
            IntStream.range(0, 3).forEach(i -> info[i] = in.nextInt());
            Arrays.stream(opBoard).forEach(x -> x.setInitType(info[1]));
            IntStream.range(1, info[0]).forEach(i -> {
                IntStream.range(0, 4).forEach(j -> info[j] = in.nextInt());
                opBoard[0].placeBlock(info[1] - 1, info[2] - 1, info[3]);
                opBoard[1].setType(info[0]);
                IntStream.range(0, 4).forEach(j -> info[j] = in.nextInt());
                opBoard[1].placeBlock(info[1] - 1, info[2] - 1, info[3]);
                opBoard[0].setType(info[0]);
                swapCache();
                Arrays.stream(opBoard).forEach(x -> x.transfer());
            });
            return this;
        }

        static class NodeInfo {
            static class SearchInfo {
                double val = 0;
                int calcd = 0;

                double value(double logf, double rate) {
                    if (calcd == 0) return random() + rate * 100;
                    return val / calcd + rate * sqrt(logf / calcd);
                }
                void update(double x) { val += x; ++calcd; }
            }
            private Map[] m = new Map[4];
            boolean[] dead = new boolean[2];
            private int calcd = 0;
            private Map<Integer, Board> b = new HashMap<Integer, Board>();

            NodeInfo init(int[][] avail) {
                Collector<Integer, ?, Map<Integer, SearchInfo>>
                    col = Collectors.toMap(x -> x, x -> new SearchInfo());
                IntStream.range(0, 4).forEach(i ->
                    m[i] = IntStream.of(avail[i]).boxed().collect(col));
                IntStream.range(0, 2).forEach(i ->
                    dead[i] = avail[2 * i + 1].length == 0);
                return this;
            }
            boolean isDead() { return dead[0] || dead[1]; }
            int[] choose(boolean isEnd) {
                ++calcd;
                double blkC = isEnd ? 0 : Args.BlkC, posC = isEnd ? 0 : Args.PosC,
                    logf = log(calcd);
                BiPredicate<SearchInfo, SearchInfo>
                    bg = (s1, s2) -> s1.value(logf, blkC) > s2.value(logf, blkC),
                    pg = (s1, s2) -> s1.value(logf, posC) > s2.value(logf, posC),
                    bl = (s1, s2) -> s1.value(logf, -blkC) < s2.value(logf, -blkC),
                    pl = (s1, s2) -> s1.value(logf, -posC) < s2.value(logf, -posC);
                Function<BiPredicate<SearchInfo, SearchInfo>,
                    BinaryOperator<Map.Entry<Integer, SearchInfo>>>
                    cmp = b -> ((e, f) -> b.test(e.getValue(), f.getValue()) ? e : f);
                BiFunction<Map<Integer, SearchInfo>,
                    BinaryOperator<Map.Entry<Integer, SearchInfo>>, Integer>
                    fnc = (m, x) -> m.entrySet().stream().reduce(x).get().getKey();
                return new int[] {
                    fnc.apply(m[0], cmp.apply(bg)), fnc.apply(m[1], cmp.apply(pl)),
                    fnc.apply(m[2], cmp.apply(bl)), fnc.apply(m[3], cmp.apply(pg))
                };
            }
            Function<int[], Integer>
                trans = a -> (a[0] << 24) + (a[1] << 16) + (a[2] << 8) + a[3];
            boolean has(int[] s) { return b.containsKey(trans.apply(s)); }
            Board find(int[] s) { return b.get(trans.apply(s)); }
            double update(int[] s, double x) {
                IntStream.range(0, 4).forEach(i ->
                    ((SearchInfo) m[i].get(s[i])).update(x));
                return x;
            }
            double add(int[] s, Board mb) {
                b.put(trans.apply(s), mb);
                return update(s, mb.evaluate());
            }
        }
        private NodeInfo info;
        private double ifDead = 0;

        void calcAvail() {
            int[][] avail = new int[4][];
            IntStream.range(0, 2).forEach(i -> {
                avail[2 * i] = opBoard[i].availBlock();
                avail[2 * i + 1] = opBoard[i].availPos();
            });
            info = new NodeInfo().init(avail);
        }
        double valDead(boolean[] dead) {
            int s1 = opBoard[0].score, s2 = opBoard[1].score;
            if (dead[0] && !dead[1] || s1 < s2) return Args.Dead;
            if (!dead[0] && dead[0] || s1 > s2) return - Args.Dead;
            return 0;
        }
        Board procStep(int[] s) {
            Board b = new Board();
            try {
                b.opBoard[0] = opBoard[0].clone();
                b.opBoard[1] = opBoard[1].clone();
            } catch (CloneNotSupportedException e) {
                e.printStackTrace();
            }
            b.opBoard[0].setType(s[0]);
            b.opBoard[0].placeBlock(Block.toX(s[1]), Block.toY(s[1]), Block.toR(s[1]));
            b.opBoard[1].setType(s[2]);
            b.opBoard[1].placeBlock(Block.toX(s[3]), Block.toY(s[3]), Block.toR(s[3]));
            b.swapCache();
            if (b.opBoard[0].transfer()) b.ifDead = Args.Dead;
            if (b.opBoard[1].transfer()) b.ifDead = - Args.Dead;
            return b;
        }
        double evaluate() {
            if (ifDead != 0) return ifDead;
            return opBoard[0].evaluate() - opBoard[1].evaluate();
        }

        double choose_expand() {
            if (ifDead != 0) return ifDead;
            if (info == null) calcAvail();
            if (info.isDead()) return valDead(info.dead);
            int[] s = info.choose(false);
            if (info.has(s)) return info.update(s, info.find(s).choose_expand());
            return info.add(s, procStep(s));
        }
        void printAns() {
            int[] ans = info.choose(true);
            System.out.format("%d %d %d %d", ans[2], Block.toX(ans[1]) + 1,
                Block.toY(ans[1]) + 1, Block.toR(ans[1]));
        }
    }

 	public static void main(String[] args) {
        Board root = new Board().read();
        while (System.nanoTime() < Args.Clk) root.choose_expand();
        root.printAns();
    }
}
