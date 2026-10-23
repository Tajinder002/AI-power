package com.autoplay;

import net.fabricmc.api.ClientModInitializer;
import net.fabricmc.fabric.api.client.event.lifecycle.v1.ClientTickEvents;
import net.fabricmc.fabric.api.client.keybinding.v1.KeyBindingHelper;
import net.fabricmc.fabric.api.client.rendering.v1.HudRenderCallback;
import net.fabricmc.loader.api.FabricLoader;
import net.minecraft.client.MinecraftClient;
import net.minecraft.client.gui.screen.DeathScreen;
import net.minecraft.client.gui.screen.Screen;
import net.minecraft.client.gui.widget.ButtonWidget;
import net.minecraft.client.network.ClientPlayerEntity;
import net.minecraft.client.option.KeyBinding;
import net.minecraft.client.util.InputUtil;
import net.minecraft.entity.Entity;
import net.minecraft.entity.LivingEntity;
import net.minecraft.entity.decoration.ArmorStandEntity;
import net.minecraft.entity.decoration.EndCrystalEntity;
import net.minecraft.entity.player.PlayerEntity;
import net.minecraft.item.BlockItem;
import net.minecraft.item.ItemStack;
import net.minecraft.item.Items;
import net.minecraft.registry.tag.ItemTags;
import net.minecraft.text.Text;
import net.minecraft.util.Hand;
import net.minecraft.util.Identifier;
import net.minecraft.util.hit.EntityHitResult;
import net.minecraft.util.hit.HitResult;
import net.minecraft.util.math.MathHelper;
import net.minecraft.util.math.Vec3d;
import org.lwjgl.glfw.GLFW;

import java.io.*;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.HashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Random;
import java.util.UUID;

/**
 * AutoPlay AI - one mod, two ways to teach it. Press K to open the menu:
 *
 *   1) Start AutoPlay  : the AI plays and learns by trial and error (with a built-in teacher at first).
 *   2) Watch mode      : YOU play normally. The AI records what you do (and what other players nearby do)
 *                        and learns to copy it - including crystal PvP: crystals, obsidian, hotbar swaps, eating.
 *
 * Press K again at any time to stop. Everything it learned is saved in the config folder:
 *   config/autoplay-brain.bin  (the neural network)   config/autoplay-demos.bin  (recorded fights)
 */
public class AutoPlayClient implements ClientModInitializer {

    private enum Mode { OFF, AUTOPLAY, WATCH }

    // ----------------------------------------------------------- tunables
    private static final double TARGET_RANGE = 32.0;
    private static final int BATCH = 128;               // learn every N ticks (and on every death)
    private static final float[] YAW_BINS = {-40f, -15f, -5f, 0f, 5f, 15f, 40f};
    private static final float[] PITCH_BINS = {-15f, -5f, 0f, 5f, 15f};

    // raw observation indices (what the AI "sees"; RAW_N must equal Brain.IN)
    private static final int HP = 0, FOOD = 1, HAS = 2, DIST = 3, YAW = 4, PITCH = 5, DY = 6,
            VX = 7, VY = 8, VZ = 9, GROUND = 10, CD = 11, EHP = 12,
            HELD = 13,                        // 13..29: one flag per held-item type (17 types)
            OFF_TOTEM = 30, OFF_SHIELD = 31, OFF_OTHER = 32,
            SLOT_LOC = 33,                    // 33..44: which hotbar slot holds each key item (0 = none)
            HAS_C = 45, C_DIST = 46, C_YAW = 47, C_PITCH = 48,
            LOOK_BLK = 49, BLK_TO_E = 50, C_TO_E = 51,
            S_USING = 52, S_BLOCK = 53, S_SNEAK = 54, S_FALL = 55,
            E_RANGED = 56, E_CRYSTAL = 57, E_HEAVY = 58, E_BLOCK = 59, E_USING = 60,
            E_VX = 61, E_VY = 62, E_VZ = 63,
            RAW_N = 64;

    // item types that get a hotbar locator (see category())
    private static final int[] HOTBAR_CATS = {1, 2, 3, 4, 7, 8, 9, 10, 12, 13, 14, 16};

    // scale each raw number to roughly -1..1 for the network
    private static final double[] SCALE = new double[RAW_N];
    static {
        Arrays.fill(SCALE, 1.0);
        SCALE[HP] = 1 / 20.0;
        SCALE[FOOD] = 1 / 20.0;
        SCALE[DIST] = 1 / 32.0;
        SCALE[YAW] = 1 / 180.0;
        SCALE[PITCH] = 1 / 90.0;
        SCALE[DY] = 1 / 8.0;
        SCALE[VX] = SCALE[VY] = SCALE[VZ] = 4;
        SCALE[EHP] = 1 / 20.0;
        SCALE[C_DIST] = 1 / 16.0;
        SCALE[C_YAW] = 1 / 180.0;
        SCALE[C_PITCH] = 1 / 90.0;
        SCALE[BLK_TO_E] = 1 / 8.0;
        SCALE[C_TO_E] = 1 / 8.0;
        SCALE[S_FALL] = 0.1;
        SCALE[E_VX] = SCALE[E_VY] = SCALE[E_VZ] = 4;
    }

    // action head indices (see Brain.HEADS)
    private static final int A_FWD = 0, A_STR = 1, A_JUMP = 2, A_SPR = 3, A_ATK = 4,
            A_USE = 5, A_SLOT = 6, A_YAW = 7, A_PITCH = 8, A_SNEAK = 9;

    private static KeyBinding toggleKey;

    private final Brain brain = new Brain();
    private Path savePath;
    private Path demoPath;

    private Mode mode = Mode.OFF;
    private boolean learnOthers = true;

    private LivingEntity target;
    private double[] prevRaw;
    private boolean deathReported = false;
    private int ticksDead = 0;
    private int episodeTicks = 0;
    private long totalTicks = 0;
    private boolean useTeacher = false;
    private int watchSamples = 0;

    // smooth aiming: the AI picks a turn SPEED once per tick; the camera is rotated a little every frame
    private float aimVelYaw = 0f, aimVelPitch = 0f;   // degrees per tick
    private long lastFrameNs = 0;

    private Track meTrack = new Track();
    private final Map<UUID, Track> tracks = new HashMap<>();

    /** What we remembered about a player on the previous tick (to work out what they did). */
    private static final class Track {
        boolean init;
        double px, py, pz;
        float pyaw, ppitch, pswing;
        int pslot;
        double peakY;                 // highest point since last on the ground (for falling attacks)
        Entity lastTarget;            // who we were fighting last tick (to measure their speed)
        double tx, ty, tz;

        void advance(PlayerEntity a) {
            px = a.getX();
            py = a.getY();
            pz = a.getZ();
            pyaw = a.getYaw();
            ppitch = a.getPitch();
            pswing = a.getHandSwingProgress(0f);
            pslot = a.getInventory().getSelectedSlot();
            init = true;
        }
    }

    @Override
    public void onInitializeClient() {
        savePath = FabricLoader.getInstance().getConfigDir().resolve("autoplay-brain.bin");
        demoPath = FabricLoader.getInstance().getConfigDir().resolve("autoplay-demos.bin");
        brain.load(savePath);
        brain.loadDemos(demoPath);

        KeyBinding.Category category = KeyBinding.Category.create(Identifier.of("autoplay", "main"));
        toggleKey = KeyBindingHelper.registerKeyBinding(
                new KeyBinding("key.autoplay.toggle", InputUtil.Type.KEYSYM, GLFW.GLFW_KEY_K, category));

        ClientTickEvents.END_CLIENT_TICK.register(this::onTick);
        HudRenderCallback.EVENT.register((drawContext, tickCounter) -> onFrame());
    }

    // ------------------------------------------------------------ start / stop

    private void startMode(Mode m) {
        MinecraftClient mc = MinecraftClient.getInstance();
        mode = m;
        target = null;
        prevRaw = null;
        deathReported = false;
        episodeTicks = 0;
        watchSamples = 0;
        meTrack = new Track();
        tracks.clear();
        brain.discard();
        aimVelYaw = 0f;
        aimVelPitch = 0f;
        say(mc, m == Mode.AUTOPLAY ? "AutoPlay ON: the AI is playing and learning"
                : "Watch mode ON: play normally, the AI is learning from you");
    }

    private void stop(MinecraftClient mc) {
        mode = Mode.OFF;
        aimVelYaw = 0f;
        aimVelPitch = 0f;
        brain.discard();
        KeyBinding.unpressAll();
        brain.save(savePath);
        brain.saveDemos(demoPath);
        say(mc, "AutoPlay OFF (everything saved)");
    }

    private void say(MinecraftClient mc, String msg) {
        if (mc.player != null) mc.player.sendMessage(Text.literal(msg), true);
    }

    // -------------------------------------------------------------------- tick

    private void onTick(MinecraftClient mc) {
        while (toggleKey.wasPressed()) {
            if (mode != Mode.OFF) stop(mc);
            else if (mc.player != null && mc.currentScreen == null) mc.setScreen(new ControlScreen());
        }
        if (mode == Mode.OFF) return;

        ClientPlayerEntity p = mc.player;
        if (p == null || mc.world == null) return;

        if (mode == Mode.WATCH) watchTick(mc, p);
        else autoTick(mc, p);
    }

    // ------------------------------------------------------ smooth aiming (every frame)

    /** Runs every rendered frame (60+ per second): turns the camera a small step, like a mouse would. */
    private void onFrame() {
        long now = System.nanoTime();
        float dt = lastFrameNs == 0 ? 0f : (now - lastFrameNs) / 50_000_000f; // in game ticks
        lastFrameNs = now;
        if (mode != Mode.AUTOPLAY) return;

        MinecraftClient mc = MinecraftClient.getInstance();
        ClientPlayerEntity p = mc.player;
        if (p == null || mc.currentScreen != null || p.isDead()) return;

        dt = Math.min(dt, 2f);
        // changeLookDirection is what the mouse uses (it multiplies by 0.15 degrees per unit)
        p.changeLookDirection(aimVelYaw * dt / 0.15, aimVelPitch * dt / 0.15);
    }

    // ---------------------------------------------------------- mode 1: AutoPlay

    private void autoTick(MinecraftClient mc, ClientPlayerEntity p) {
        // ---- dead: report once, then respawn
        if (p.isDead() || mc.currentScreen instanceof DeathScreen) {
            if (!deathReported) onDeath();
            if (ticksDead++ % 20 == 10) p.requestRespawn();
            return;
        }
        deathReported = false;
        if (mc.currentScreen != null) return; // menu/chat open: don't act

        // ---- target tracking (locked until it dies or vanishes)
        int killed = 0;
        if (target != null && (!target.isAlive() || target.isRemoved())) {
            killed = 1;
            brain.kills++;
            target = null;
        }
        if (target == null) target = pickTarget(mc, p);

        double[] raw = observe(mc, p, target, meTrack, true);
        meTrack.advance(p);
        double[] x = normalize(raw);

        // ---- reward for the previous action, learn if the batch is full
        if (brain.hasPending() && prevRaw != null) {
            brain.reward(reward(prevRaw, raw, killed), false);
            if (brain.size() >= BATCH) brain.update(brain.value(x));
        }

        // ---- choose and apply a new action (teacher drives part of the time at first)
        if (totalTicks % 20 == 0) useTeacher = brain.rnd.nextDouble() < brain.teacherProb;
        brain.teacherProb = Math.max(0.05, brain.teacherProb - 0.00003);
        applyAction(mc, p, brain.act(x, useTeacher ? teacherAction(raw) : null));
        prevRaw = raw;
        episodeTicks++;
        totalTicks++;

        if (totalTicks % 2000 == 0) brain.save(savePath);
        if (totalTicks % 20 == 0) {
            say(mc, String.format(Locale.ROOT, "AutoPlay | deaths %d | kills %d | best life %ds | this life %ds | teacher %d%%",
                    brain.deaths, brain.kills, brain.bestTicks / 20, episodeTicks / 20,
                    (int) Math.round(brain.teacherProb * 100)));
        }
    }

    private void onDeath() {
        deathReported = true;
        ticksDead = 0;
        aimVelYaw = 0f;
        aimVelPitch = 0f;
        KeyBinding.unpressAll();
        if (brain.hasPending()) {
            brain.reward(-5.0, true);
            brain.update(0.0); // learn from this death right now
        }
        brain.deaths++;
        brain.bestTicks = Math.max(brain.bestTicks, episodeTicks);
        episodeTicks = 0;
        target = null;
        prevRaw = null;
        meTrack = new Track();
        if (brain.deaths % 5 == 0) brain.save(savePath);
    }

    // ----------------------------------------------------------- mode 2: Watch

    private void watchTick(MinecraftClient mc, ClientPlayerEntity p) {
        if (mc.currentScreen != null || p.isDead()) return;
        totalTicks++;

        int seen = 0;
        for (Entity e : mc.world.getEntities()) {
            if (!(e instanceof PlayerEntity)) continue;
            PlayerEntity actor = (PlayerEntity) e;
            boolean isMe = actor == p;
            if (!isMe && (!learnOthers || p.distanceTo(actor) > 48)) continue;
            if (!actor.isAlive() || actor.isSpectator()) continue;
            seen++;

            Track t = isMe ? meTrack : tracks.computeIfAbsent(actor.getUuid(), k -> new Track());
            LivingEntity tgt = pickTarget(mc, actor);
            double[] raw = observe(mc, actor, tgt, t, isMe);
            if (t.init && tgt != null && raw[DIST] < 20) {
                brain.addDemo(normalize(raw), inferAction(mc, actor, t, isMe));
                watchSamples++;
            }
            t.advance(actor);
        }

        // learn from what was recorded
        if (brain.newDemos >= 32) {
            brain.newDemos = 0;
            brain.trainDemos(1, 128);
        }

        if (totalTicks % 6000 == 0) {
            brain.save(savePath);
            brain.saveDemos(demoPath);
        }
        if (totalTicks % 20 == 0) {
            say(mc, String.format(Locale.ROOT, "Watching | players seen %d | samples this session %d | total stored %d",
                    seen, watchSamples, brain.dCount));
        }
    }

    /** Work out what a player did this tick (their "action"), so the AI can copy it. */
    private int[] inferAction(MinecraftClient mc, PlayerEntity actor, Track t, boolean isMe) {
        int[] a = new int[Brain.ACTN];
        double vx = actor.getX() - t.px, vy = actor.getY() - t.py, vz = actor.getZ() - t.pz;
        float yawDelta = MathHelper.wrapDegrees(actor.getYaw() - t.pyaw);
        float pitchDelta = actor.getPitch() - t.ppitch;
        int heldCat = category(actor.getMainHandStack());

        if (isMe) {
            // my real key presses
            a[A_FWD] = mc.options.forwardKey.isPressed() ? 1 : (mc.options.backKey.isPressed() ? 2 : 0);
            a[A_STR] = mc.options.leftKey.isPressed() ? 1 : (mc.options.rightKey.isPressed() ? 2 : 0);
            a[A_JUMP] = mc.options.jumpKey.isPressed() ? 1 : 0;
            a[A_ATK] = mc.options.attackKey.isPressed() ? 1 : 0;
            a[A_USE] = mc.options.useKey.isPressed() ? 1 : 0;
            a[A_SNEAK] = mc.options.sneakKey.isPressed() ? 1 : 0;
            int slot = actor.getInventory().getSelectedSlot();
            a[A_SLOT] = slot != t.pslot ? slot + 1 : 0;
        } else {
            // other players: guess from how they moved and swung
            double yawRad = Math.toRadians(actor.getYaw());
            double fwd = vx * -Math.sin(yawRad) + vz * Math.cos(yawRad);
            double right = vx * -Math.cos(yawRad) + vz * -Math.sin(yawRad);
            a[A_FWD] = fwd > 0.05 ? 1 : (fwd < -0.05 ? 2 : 0);
            a[A_STR] = right < -0.05 ? 1 : (right > 0.05 ? 2 : 0);
            a[A_JUMP] = (!actor.isOnGround() && vy > 0.1) ? 1 : 0;
            float sw = actor.getHandSwingProgress(0f);
            boolean swung = sw > 0 && t.pswing == 0;
            boolean usesItem = heldCat == 7 || heldCat == 8 || heldCat == 10 || heldCat == 12
                    || heldCat == 13 || heldCat == 14 || heldCat == 15 || heldCat == 16;
            a[A_ATK] = (swung && !usesItem) ? 1 : 0;
            a[A_USE] = ((swung && usesItem) || actor.isUsingItem()) ? 1 : 0;
            a[A_SNEAK] = actor.isSneaking() ? 1 : 0;
            a[A_SLOT] = 0;
        }
        a[A_SPR] = actor.isSprinting() ? 1 : 0;
        a[A_YAW] = nearest(YAW_BINS, yawDelta);
        a[A_PITCH] = nearest(PITCH_BINS, pitchDelta);
        return a;
    }

    // ------------------------------------------------------------- observation

    /** What kind of item is this? Lets the AI tell swords, axes, maces, bows, crystals, pearls... apart. */
    private static int category(ItemStack s) {
        if (s == null || s.isEmpty()) return 0;
        if (s.isIn(ItemTags.SWORDS)) return 1;
        if (s.isIn(ItemTags.AXES)) return 2;
        if (s.isOf(Items.MACE)) return 3;
        if (s.isOf(Items.BOW) || s.isOf(Items.CROSSBOW)) return 4;
        if (s.isOf(Items.TRIDENT)) return 5;
        if (s.isOf(Items.SHIELD)) return 6;
        if (s.isOf(Items.END_CRYSTAL)) return 7;
        if (s.isOf(Items.RESPAWN_ANCHOR) || s.isOf(Items.GLOWSTONE)) return 15;
        if (s.isOf(Items.COBWEB)) return 16;
        if (s.getItem() instanceof BlockItem) return 8;
        if (s.isOf(Items.GOLDEN_APPLE) || s.isOf(Items.ENCHANTED_GOLDEN_APPLE)) return 9;
        if (s.isOf(Items.ENDER_PEARL)) return 10;
        if (s.isOf(Items.TOTEM_OF_UNDYING)) return 11;
        if (s.isOf(Items.WIND_CHARGE)) return 12;
        if (s.isOf(Items.POTION) || s.isOf(Items.SPLASH_POTION) || s.isOf(Items.LINGERING_POTION)) return 13;
        if (s.isOf(Items.WATER_BUCKET) || s.isOf(Items.LAVA_BUCKET)) return 14;
        return 17;
    }

    private double[] observe(MinecraftClient mc, PlayerEntity a, LivingEntity tgt, Track t, boolean isMe) {
        double[] o = new double[RAW_N];
        o[HP] = a.getHealth();
        o[FOOD] = isMe ? a.getHungerManager().getFoodLevel() : 20;
        o[DIST] = TARGET_RANGE;
        Vec3d eye = a.getEyePos();
        Vec3d tc = null;
        if (tgt != null) {
            tc = tgt.getBoundingBox().getCenter();
            double[] ae = aim(a, eye, tc);
            o[HAS] = 1;
            o[YAW] = ae[0];
            o[PITCH] = ae[1];
            o[DIST] = ae[2];
            o[DY] = ae[3];
            o[EHP] = tgt.getHealth();

            // what the enemy is doing / holding and how fast it moves
            int ec = category(tgt.getMainHandStack());
            o[E_RANGED] = (ec == 4 || ec == 5) ? 1 : 0;
            o[E_CRYSTAL] = (ec == 7 || ec == 15) ? 1 : 0;
            o[E_HEAVY] = (ec == 2 || ec == 3) ? 1 : 0;
            o[E_BLOCK] = tgt.isBlocking() ? 1 : 0;
            o[E_USING] = tgt.isUsingItem() ? 1 : 0;
            if (t.lastTarget == tgt) {
                o[E_VX] = tgt.getX() - t.tx;
                o[E_VY] = tgt.getY() - t.ty;
                o[E_VZ] = tgt.getZ() - t.tz;
            }
            t.tx = tgt.getX();
            t.ty = tgt.getY();
            t.tz = tgt.getZ();
        }
        t.lastTarget = tgt;

        if (t.init) {
            o[VX] = a.getX() - t.px;
            o[VY] = a.getY() - t.py;
            o[VZ] = a.getZ() - t.pz;
        }
        o[GROUND] = a.isOnGround() ? 1 : 0;
        o[CD] = isMe ? a.getAttackCooldownProgress(0f) : 1.0;

        // held items
        int cat = category(a.getMainHandStack());
        if (cat >= 1 && cat <= 17) o[HELD + cat - 1] = 1;
        int oc = category(a.getOffHandStack());
        o[OFF_TOTEM] = oc == 11 ? 1 : 0;
        o[OFF_SHIELD] = oc == 6 ? 1 : 0;
        o[OFF_OTHER] = (oc != 0 && oc != 11 && oc != 6) ? 1 : 0;
        if (isMe) { // we can only see our own hotbar
            for (int i = 0; i < 9; i++) {
                int c = category(a.getInventory().getStack(i));
                for (int k = 0; k < HOTBAR_CATS.length; k++) {
                    if (HOTBAR_CATS[k] == c && o[SLOT_LOC + k] == 0) o[SLOT_LOC + k] = (i + 1) / 9.0;
                }
            }
        }

        // own state
        o[S_USING] = a.isUsingItem() ? 1 : 0;
        o[S_BLOCK] = a.isBlocking() ? 1 : 0;
        o[S_SNEAK] = a.isSneaking() ? 1 : 0;
        double y = a.getY();
        if (!t.init) t.peakY = y;
        t.peakY = a.isOnGround() ? y : Math.max(t.peakY, y);
        o[S_FALL] = Math.max(0, t.peakY - y);

        // nearest end crystal
        EndCrystalEntity best = null;
        double bestD = 16.0;
        for (Entity e : mc.world.getEntities()) {
            if (!(e instanceof EndCrystalEntity)) continue;
            double d = a.distanceTo(e);
            if (d < bestD) {
                bestD = d;
                best = (EndCrystalEntity) e;
            }
        }
        if (best != null) {
            Vec3d cc = best.getBoundingBox().getCenter();
            double[] ce = aim(a, eye, cc);
            o[HAS_C] = 1;
            o[C_YAW] = ce[0];
            o[C_PITCH] = ce[1];
            o[C_DIST] = ce[2];
            if (tc != null) o[C_TO_E] = cc.distanceTo(tc);
        }

        // block under the crosshair (where obsidian/crystals/webs would go)
        HitResult hr = a.raycast(5.0, 0f, false);
        if (hr.getType() == HitResult.Type.BLOCK) {
            o[LOOK_BLK] = 1;
            if (tc != null) o[BLK_TO_E] = hr.getPos().distanceTo(tc);
        }
        return o;
    }

    /** {yaw error, pitch error, distance, height difference} from this player's eyes to a point. */
    private static double[] aim(PlayerEntity a, Vec3d eye, Vec3d to) {
        Vec3d d = to.subtract(eye);
        double hor = Math.sqrt(d.x * d.x + d.z * d.z);
        float wantYaw = (float) Math.toDegrees(Math.atan2(-d.x, d.z));
        float wantPitch = (float) -Math.toDegrees(Math.atan2(d.y, hor));
        return new double[]{MathHelper.wrapDegrees(wantYaw - a.getYaw()), wantPitch - a.getPitch(), d.length(), d.y};
    }

    private static double[] normalize(double[] r) {
        double[] x = new double[RAW_N];
        for (int i = 0; i < RAW_N; i++) x[i] = Math.max(-3, Math.min(3, r[i] * SCALE[i]));
        return x;
    }

    // ------------------------------------------------------------------ reward

    private static double reward(double[] a, double[] b, int killed) {
        double r = -0.001;                       // tiny time cost: don't idle
        if (killed == 1) r += 5.0;               // kill
        r -= 0.1 * Math.max(0, a[HP] - b[HP]);   // damage taken
        if (killed == 0 && a[HAS] == 1 && b[HAS] == 1) {
            r += 0.15 * Math.max(0, a[EHP] - b[EHP]);               // damage dealt (swords AND crystals)
            double aimA = Math.abs(a[YAW]) / 180 + Math.abs(a[PITCH]) / 90;
            double aimB = Math.abs(b[YAW]) / 180 + Math.abs(b[PITCH]) / 90;
            r += 0.5 * (aimA - aimB);                                // turned toward enemy
            r += 0.05 * (a[DIST] - b[DIST]);                         // got closer
            if (Math.abs(b[YAW]) < 10 && Math.abs(b[PITCH]) < 10 && b[DIST] < 3.5) r += 0.01; // aimed & in reach
        }
        return Math.max(-6, Math.min(6, r));
    }

    // ----------------------------------------------------------------- teacher

    /** Simple hand-written fighter: face the enemy, walk up, hit when in reach. The AI copies it early on. */
    private static int[] teacherAction(double[] r) {
        boolean has = r[HAS] == 1;
        double dist = r[DIST];
        int forward = 0, sprint = 0, attack = 0;
        if (has) {
            forward = dist > 2.5 ? 1 : 0;
            sprint = dist > 5 ? 1 : 0;
            if (dist < 3.3 && Math.abs(r[YAW]) < 15 && Math.abs(r[PITCH]) < 20 && r[CD] > 0.9) attack = 1;
        }
        int yaw = has ? nearest(YAW_BINS, (float) (0.4 * r[YAW])) : 3;
        int pitch = has ? nearest(PITCH_BINS, (float) (0.4 * r[PITCH])) : 2;
        int[] a = new int[Brain.ACTN];
        a[A_FWD] = forward;
        a[A_SPR] = sprint;
        a[A_ATK] = attack;
        a[A_YAW] = yaw;
        a[A_PITCH] = pitch;
        // not holding a sword but has one in the hotbar? switch to it
        if (r[HELD] == 0 && r[SLOT_LOC] > 0) a[A_SLOT] = (int) Math.round(r[SLOT_LOC] * 9);
        return a;
    }

    private static int nearest(float[] bins, float want) {
        int best = 0;
        for (int i = 1; i < bins.length; i++) {
            if (Math.abs(bins[i] - want) < Math.abs(bins[best] - want)) best = i;
        }
        return best;
    }

    // ----------------------------------------------------------------- actions

    private void applyAction(MinecraftClient mc, ClientPlayerEntity p, int[] a) {
        mc.options.forwardKey.setPressed(a[A_FWD] == 1);
        mc.options.backKey.setPressed(a[A_FWD] == 2);
        mc.options.leftKey.setPressed(a[A_STR] == 1);
        mc.options.rightKey.setPressed(a[A_STR] == 2);
        mc.options.jumpKey.setPressed(a[A_JUMP] == 1);
        mc.options.sprintKey.setPressed(a[A_SPR] == 1 && a[A_FWD] == 1);
        mc.options.useKey.setPressed(a[A_USE] == 1);
        mc.options.sneakKey.setPressed(a[A_SNEAK] == 1);

        if (a[A_SLOT] > 0) p.getInventory().setSelectedSlot(a[A_SLOT] - 1);

        // ease toward the wanted turn speed (no sudden whips); onFrame() does the actual turning
        aimVelYaw += (YAW_BINS[a[A_YAW]] - aimVelYaw) * 0.3f;
        aimVelPitch += (PITCH_BINS[a[A_PITCH]] - aimVelPitch) * 0.3f;

        if (a[A_ATK] == 1) {
            HitResult hit = mc.crosshairTarget;
            if (hit instanceof EntityHitResult ehr && mc.interactionManager != null) {
                mc.interactionManager.attackEntity(p, ehr.getEntity());
                p.swingHand(Hand.MAIN_HAND);
            }
        }
    }

    /** Nearest living entity in range for this player; real players are always preferred over mobs. */
    private LivingEntity pickTarget(MinecraftClient mc, PlayerEntity actor) {
        LivingEntity best = null;
        double bestScore = Double.MAX_VALUE;
        for (Entity e : mc.world.getEntities()) {
            if (!(e instanceof LivingEntity) || e == actor || e instanceof ArmorStandEntity) continue;
            LivingEntity le = (LivingEntity) e;
            if (!le.isAlive() || le.isSpectator()) continue;
            double d = actor.distanceTo(le);
            if (d > TARGET_RANGE) continue;
            double score = d - (le instanceof PlayerEntity ? 1000.0 : 0.0);
            if (score < bestScore) {
                bestScore = score;
                best = le;
            }
        }
        return best;
    }

    // ====================================================================
    //  The menu (press K)
    // ====================================================================
    private class ControlScreen extends Screen {
        ControlScreen() {
            super(Text.literal("AutoPlay AI"));
        }

        @Override
        protected void init() {
            int w = 280;
            int x = this.width / 2 - w / 2;
            int y = this.height / 2 - 80;

            ButtonWidget header = ButtonWidget.builder(Text.literal(String.format(Locale.ROOT,
                    "AutoPlay AI | recorded fights: %d | deaths: %d", brain.dCount, brain.deaths)), b -> { })
                    .dimensions(x, y, w, 20).build();
            header.active = false;
            addDrawableChild(header);

            addDrawableChild(ButtonWidget.builder(Text.literal("1) Start AutoPlay - AI plays and learns"), b -> {
                startMode(Mode.AUTOPLAY);
                close();
            }).dimensions(x, y + 30, w, 20).build());

            addDrawableChild(ButtonWidget.builder(Text.literal("2) Watch mode - I play, AI watches and learns"), b -> {
                startMode(Mode.WATCH);
                close();
            }).dimensions(x, y + 55, w, 20).build());

            addDrawableChild(ButtonWidget.builder(Text.literal(othersLabel()), b -> {
                learnOthers = !learnOthers;
                b.setMessage(Text.literal(othersLabel()));
            }).dimensions(x, y + 80, w, 20).build());

            addDrawableChild(ButtonWidget.builder(Text.literal("Reset what the AI learned (keeps recorded fights)"), b -> {
                brain.resetWeights();
                brain.save(savePath);
                b.setMessage(Text.literal("AI brain reset"));
            }).dimensions(x, y + 105, w, 20).build());

            addDrawableChild(ButtonWidget.builder(Text.literal("Close"), b -> close())
                    .dimensions(x, y + 135, w, 20).build());
        }

        private String othersLabel() {
            return "Watch mode also learns from other players: " + (learnOthers ? "ON" : "OFF");
        }
    }

    // BRAIN-START
    // =====================================================================
    //  The brain: small actor-critic network (64 -> 96 -> 96 -> 38 + value)
    //  Actions are 10 independent choices:
    //  forward/back(3) strafe(3) jump(2) sprint(2) attack(2) use(2) hotbar(10) yaw(7) pitch(5) sneak(2)
    //  It learns two ways: trial and error (A2C) and copying recorded play (imitation).
    // =====================================================================
    static final class Brain {
        static final int IN = 64, H = 96, OUT = 38, ACTN = 10;
        static final int[] HEADS = {3, 3, 2, 2, 2, 2, 10, 7, 5, 2};
        static final double GAMMA = 0.99, LAMBDA = 0.95, LR = 0.003, ENT = 0.01, VC = 0.5, MAX_GRAD = 5.0;

        // parameter layout inside one flat array
        static final int O_W1 = 0;
        static final int O_B1 = O_W1 + H * IN;
        static final int O_W2 = O_B1 + H;
        static final int O_B2 = O_W2 + H * H;
        static final int O_WP = O_B2 + H;
        static final int O_BP = O_WP + OUT * H;
        static final int O_WV = O_BP + OUT;
        static final int O_BV = O_WV + H;
        static final int N = O_BV + 1;
        static final int MAGIC = 0xA17B0004;
        static final int CAP = 1024;     // trial-and-error buffer
        static final int CAPD = 20000;   // recorded demonstrations

        final double[] w = new double[N];
        final double[] g = new double[N];
        final double[] m = new double[N];
        final double[] v = new double[N];
        int adamT = 0;
        final Random rnd = new Random();

        // scratch space for forward/backward
        final double[] h1 = new double[H], h2 = new double[H];
        final double[] logits = new double[OUT], probs = new double[OUT], dl = new double[OUT];
        final double[] dh1 = new double[H], dh2 = new double[H];

        // pending transition (observation + action waiting for its reward)
        double[] pObs;
        int[] pAct;
        double pVal;
        boolean pTeacher = false;
        boolean pending = false;

        // trial-and-error buffer
        final double[][] bObs = new double[CAP][];
        final int[][] bAct = new int[CAP][];
        final double[] bRew = new double[CAP], bVal = new double[CAP];
        final boolean[] bDone = new boolean[CAP], bTeacher = new boolean[CAP];
        int n = 0;

        // recorded demonstrations (ring buffer)
        final float[][] dObs = new float[CAPD][IN];
        final byte[][] dAct = new byte[CAPD][ACTN];
        int dCount = 0, dHead = 0, newDemos = 0;

        double teacherProb = 0.8; // how often the built-in teacher drives; fades over time

        // lifetime stats (saved with the weights)
        int deaths = 0, kills = 0, bestTicks = 0;

        Brain() {
            resetWeights();
        }

        void resetWeights() {
            init(O_W1, H * IN, Math.sqrt(1.0 / IN));
            init(O_B1, H, 0);
            init(O_W2, H * H, Math.sqrt(1.0 / H));
            init(O_B2, H, 0);
            init(O_WP, OUT * H, 0.01);
            init(O_BP, OUT, 0);
            init(O_WV, H, 0.1);
            w[O_BV] = 0;
            Arrays.fill(m, 0);
            Arrays.fill(v, 0);
            adamT = 0;
            teacherProb = 0.8;
            deaths = 0;
            kills = 0;
            bestTicks = 0;
            // sane starting habits: walk forward, rarely jump/turn/use, keep the hotbar slot
            w[O_BP + 1] += 1.0;    // forward
            w[O_BP + 6] += 1.5;    // jump: mostly don't
            w[O_BP + 9] += 0.5;    // sprint
            w[O_BP + 11] += 0.5;   // attack
            w[O_BP + 12] += 1.5;   // use item: mostly don't
            w[O_BP + 14] += 3.0;   // hotbar: mostly keep
            w[O_BP + 27] += 1.5;   // yaw: mostly no turn
            w[O_BP + 33] += 1.5;   // pitch: mostly no turn
            w[O_BP + 36] += 1.5;   // sneak: mostly don't
        }

        private void init(int off, int len, double scale) {
            for (int i = 0; i < len; i++) w[off + i] = scale == 0 ? 0 : rnd.nextGaussian() * scale;
        }

        boolean hasPending() { return pending; }
        int size() { return n; }
        void discard() { n = 0; pending = false; }

        /** Runs the network on x; fills h1,h2,logits,probs; returns the value estimate. */
        double forward(double[] x) {
            for (int j = 0; j < H; j++) {
                double s = w[O_B1 + j];
                int b = O_W1 + j * IN;
                for (int i = 0; i < IN; i++) s += w[b + i] * x[i];
                h1[j] = Math.tanh(s);
            }
            for (int k = 0; k < H; k++) {
                double s = w[O_B2 + k];
                int b = O_W2 + k * H;
                for (int j = 0; j < H; j++) s += w[b + j] * h1[j];
                h2[k] = Math.tanh(s);
            }
            for (int o = 0; o < OUT; o++) {
                double s = w[O_BP + o];
                int b = O_WP + o * H;
                for (int k = 0; k < H; k++) s += w[b + k] * h2[k];
                logits[o] = s;
            }
            double val = w[O_BV];
            for (int k = 0; k < H; k++) val += w[O_WV + k] * h2[k];

            int hs = 0;
            for (int size : HEADS) {
                double max = -1e30;
                for (int i = 0; i < size; i++) max = Math.max(max, logits[hs + i]);
                double sum = 0;
                for (int i = 0; i < size; i++) {
                    probs[hs + i] = Math.exp(logits[hs + i] - max);
                    sum += probs[hs + i];
                }
                for (int i = 0; i < size; i++) probs[hs + i] /= sum;
                hs += size;
            }
            return val;
        }

        double value(double[] x) { return forward(x); }

        /** Pick an action (sample the policy, or use `forced` from the teacher) and remember it until its reward arrives. */
        int[] act(double[] x, int[] forced) {
            double val = forward(x);
            int[] a = new int[ACTN];
            int hs = 0;
            for (int h = 0; h < HEADS.length; h++) {
                if (forced != null) {
                    a[h] = forced[h];
                } else {
                    double r = rnd.nextDouble(), c = 0;
                    int pick = HEADS[h] - 1;
                    for (int i = 0; i < HEADS[h]; i++) {
                        c += probs[hs + i];
                        if (r < c) { pick = i; break; }
                    }
                    a[h] = pick;
                }
                hs += HEADS[h];
            }
            pTeacher = forced != null;
            pObs = x.clone();
            pAct = a;
            pVal = val;
            pending = true;
            return a;
        }

        /** Attach the reward to the pending action and store the transition. */
        void reward(double r, boolean done) {
            if (!pending || n >= CAP) { pending = false; return; }
            bObs[n] = pObs;
            bAct[n] = pAct;
            bRew[n] = r;
            bVal[n] = pVal;
            bDone[n] = done;
            bTeacher[n] = pTeacher;
            n++;
            pending = false;
        }

        /** Adds one gradient sample to g. adv = how much to push toward the action taken (1.0 = copy it). */
        private void accumulate(double[] x, int[] a, double adv, double ret, boolean valueLoss, double entW) {
            double val = forward(x);

            int hs = 0;
            for (int h = 0; h < HEADS.length; h++) {
                int sz = HEADS[h];
                double ent = 0;
                for (int i = 0; i < sz; i++) ent -= probs[hs + i] * Math.log(probs[hs + i] + 1e-12);
                for (int i = 0; i < sz; i++) {
                    double p = probs[hs + i];
                    dl[hs + i] = adv * (p - (i == a[h] ? 1 : 0)) + entW * p * (Math.log(p + 1e-12) + ent);
                }
                hs += sz;
            }
            double dv = valueLoss ? VC * (val - ret) : 0.0;

            // value + policy heads
            g[O_BV] += dv;
            for (int k = 0; k < H; k++) {
                g[O_WV + k] += dv * h2[k];
                dh2[k] = dv * w[O_WV + k];
            }
            for (int o = 0; o < OUT; o++) {
                double d = dl[o];
                g[O_BP + o] += d;
                int b = O_WP + o * H;
                for (int k = 0; k < H; k++) {
                    g[b + k] += d * h2[k];
                    dh2[k] += d * w[b + k];
                }
            }
            // hidden layer 2
            Arrays.fill(dh1, 0);
            for (int k = 0; k < H; k++) {
                double dz = dh2[k] * (1 - h2[k] * h2[k]);
                g[O_B2 + k] += dz;
                int b = O_W2 + k * H;
                for (int j = 0; j < H; j++) {
                    g[b + j] += dz * h1[j];
                    dh1[j] += dz * w[b + j];
                }
            }
            // hidden layer 1
            for (int j = 0; j < H; j++) {
                double dz = dh1[j] * (1 - h1[j] * h1[j]);
                g[O_B1 + j] += dz;
                int b = O_W1 + j * IN;
                for (int i = 0; i < IN; i++) g[b + i] += dz * x[i];
            }
        }

        /** Average the gradient over `count` samples, clip it, and take one Adam step. */
        private void step(int count) {
            double norm = 0;
            for (int i = 0; i < N; i++) {
                g[i] /= count;
                norm += g[i] * g[i];
            }
            norm = Math.sqrt(norm);
            double scale = norm > MAX_GRAD ? MAX_GRAD / norm : 1.0;
            adamT++;
            double c1 = 1 - Math.pow(0.9, adamT), c2 = 1 - Math.pow(0.999, adamT);
            for (int i = 0; i < N; i++) {
                double gi = g[i] * scale;
                m[i] = 0.9 * m[i] + 0.1 * gi;
                v[i] = 0.999 * v[i] + 0.001 * gi * gi;
                w[i] -= LR * (m[i] / c1) / (Math.sqrt(v[i] / c2) + 1e-8);
            }
        }

        /** One actor-critic update (GAE advantages) over everything collected so far, plus a little imitation. */
        void update(double lastValue) {
            if (n < 8) return; // too little to learn from; keep collecting

            double[] adv = new double[n], ret = new double[n];
            double last = 0, nextV = lastValue;
            for (int t = n - 1; t >= 0; t--) {
                double nonTerm = bDone[t] ? 0 : 1;
                double delta = bRew[t] + GAMMA * nextV * nonTerm - bVal[t];
                last = delta + GAMMA * LAMBDA * nonTerm * last;
                adv[t] = last;
                ret[t] = last + bVal[t];
                nextV = bVal[t];
            }
            double mean = 0, var = 0;
            for (double a : adv) mean += a;
            mean /= n;
            for (double a : adv) var += (a - mean) * (a - mean);
            double std = Math.sqrt(var / n) + 1e-8;
            for (int t = 0; t < n; t++) adv[t] = bTeacher[t] ? 1.0 : (adv[t] - mean) / std;

            Arrays.fill(g, 0);
            for (int t = 0; t < n; t++) accumulate(bObs[t], bAct[t], adv[t], ret[t], true, ENT);
            step(n);
            n = 0;

            trainDemos(1, 64); // keep the recorded human play in the mix
        }

        // ------------------------------------------------ imitation learning
        void addDemo(double[] x, int[] a) {
            for (int i = 0; i < IN; i++) dObs[dHead][i] = (float) x[i];
            for (int i = 0; i < ACTN; i++) dAct[dHead][i] = (byte) a[i];
            dHead = (dHead + 1) % CAPD;
            dCount = Math.min(dCount + 1, CAPD);
            newDemos++;
        }

        /** Supervised learning: make the network pick the same actions as the recorded players. */
        void trainDemos(int steps, int batch) {
            if (dCount < 64) return;
            double[] x = new double[IN];
            int[] a = new int[ACTN];
            for (int s = 0; s < steps; s++) {
                Arrays.fill(g, 0);
                for (int b = 0; b < batch; b++) {
                    int i = rnd.nextInt(dCount);
                    for (int k = 0; k < IN; k++) x[k] = dObs[i][k];
                    for (int k = 0; k < ACTN; k++) a[k] = dAct[i][k];
                    accumulate(x, a, 1.0, 0.0, false, 0.0);
                }
                step(batch);
            }
        }

        // ------------------------------------------------------ save / load
        void save(Path path) {
            try (DataOutputStream out = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(path.toFile())))) {
                out.writeInt(MAGIC);
                out.writeInt(N);
                for (double d : w) out.writeDouble(d);
                out.writeInt(deaths);
                out.writeInt(kills);
                out.writeInt(bestTicks);
                out.writeDouble(teacherProb);
            } catch (IOException ignored) { }
        }

        void load(Path path) {
            File f = path.toFile();
            if (!f.exists()) return;
            try (DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(f)))) {
                if (in.readInt() != MAGIC || in.readInt() != N) return;
                double[] tmp = new double[N];
                for (int i = 0; i < N; i++) tmp[i] = in.readDouble();
                System.arraycopy(tmp, 0, w, 0, N);
                deaths = in.readInt();
                kills = in.readInt();
                bestTicks = in.readInt();
                teacherProb = in.readDouble();
            } catch (IOException ignored) { }
        }

        void saveDemos(Path path) {
            try (DataOutputStream out = new DataOutputStream(new BufferedOutputStream(new FileOutputStream(path.toFile())))) {
                out.writeInt(MAGIC);
                out.writeInt(IN);
                out.writeInt(dCount);
                for (int i = 0; i < dCount; i++) {
                    for (int k = 0; k < IN; k++) out.writeFloat(dObs[i][k]);
                    out.write(dAct[i]);
                }
            } catch (IOException ignored) { }
        }

        void loadDemos(Path path) {
            File f = path.toFile();
            if (!f.exists()) return;
            try (DataInputStream in = new DataInputStream(new BufferedInputStream(new FileInputStream(f)))) {
                if (in.readInt() != MAGIC || in.readInt() != IN) return;
                int c = Math.min(in.readInt(), CAPD);
                for (int i = 0; i < c; i++) {
                    for (int k = 0; k < IN; k++) dObs[i][k] = in.readFloat();
                    in.readFully(dAct[i]);
                }
                dCount = c;
                dHead = c % CAPD;
            } catch (IOException ignored) { }
        }
    }
    // BRAIN-END
}
